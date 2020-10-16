intrinsic RelativeBasis(K::RngPad, k::RngPad) -> []
  {The k-basis of K, compatible with repeated Eltseq}
  B := Basis(K);
  if CoefficientRing(K) eq k then
    return B;
  else
    b := RelativeBasis(CoefficientRing(K), k);
    return [i*j : j in b, i in B];
  end if;
end intrinsic;

intrinsic AbsoluteBasis(K::RngPad) -> []
  {A Qp basis for K}
  return RelativeBasis(K, PrimeRing(K));
end intrinsic;


//////////////MyNormEquation///////////////usung old version///
function solve_it(R,m,b,Prec) // MW, avoid duplicated code
  val:=Valuation(b); prec:=AbsolutePrecision(b)*Degree(R,Codomain(m)); // MW
  b:=ChangePrecision(b,Valuation(b)+Precision(R)); // MW
  gens := CUnitGroupGenerators(R:Raw:=true);
  B := Codomain(m); U := Domain(m);
  F := FreeAbelianGroup(#gens); 
  mF := hom<F -> U|[ Norm(ChangePrecision(g,Prec),B)@@m : g in gens]>;
  if not b@@m in Image(mF) then return false, _;
  else
    aFseq := Eltseq(b@@m@@mF);
    a := &*[gens[i]^aFseq[i]: i in [1..#gens]];
    a:=ChangePrecision(a,val+prec); // MW
    return true, a; end if;   end function;

intrinsic MyNormEquation(R::FldPad,m::Map,b::RngElt,Prec::RngIntElt) -> BoolElt, RngElt
{Given R/B and the map m : UnitGroup(B) -> B and an element b in B,
 this solves Norm(a) = b for a in R up to precision Prec}
  bool, b := IsCoercible(Codomain(m), b);
  require bool:
  "The third argument is not in the codomain of the second argument";
  try _:=Degree(R,Codomain(m)); bo:=true; catch e; bo:=false; end try;
  require bo: "Codomain of argument 2 not contained in argument 1";
  return solve_it(R,m,b,Prec); end intrinsic;

intrinsic MyNormEquation(R::RngPad,m::Map,b::RngElt,Prec::RngIntElt) -> BoolElt, RngElt {Given R/B and the map m : UnitGroup(B) -> B and an element b in B,
 this solves Norm(a) = b for a in R up to precision Prec  }
  bool, b := IsCoercible(Codomain(m), b);
  require bool:
   "The third argument is not in the codomain of the second argument";
  try _:=Degree(R,Codomain(m)); bo:=true; catch e; bo:=false; end try;
  require bo: "Codomain of argument 2 not contained in argument 1";
  return solve_it(R,m,b,Prec); end intrinsic;


declare verbose PrincipalUnitGroup, 4;

intrinsic PrimeRing(R::FldPad) -> .
{The PrimeField of R.}
  if IsField(R) then
    return PrimeField(R);
  else
    return PrimeRing(R);
  end if;
end intrinsic;

//--------------

function residue_system_basis(R)

  F := ResidueClassField(R);
  b := Basis(F);

  return [R!b[i] : i in [1..#b]];

end function;

//------------

function h2_is_isomorphism(R)

  p := Prime(R);
  pi := UniformizingElement(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := -p div pi^e;
  rcf := ResidueClassField(R);
  rcfy := PolynomialRing(rcf); y := rcfy.1;
  h22 := y^(p-1)-rcf!eps;
//"h22",Factorization(h22);
//Degree(h22);
//HasPRoot(R); IsIrreducible(h22);
  return not HasRoot(h22) and not Degree(h22) eq 1;
//  return IsIrreducible(h22) and not Degree(h22) eq 1;
end function;


//////Modified fin_w1(R) by Ali+Claus to find generators fast///////

function find_w1(R)
// subroutine for residue_system_basis_II(
  rf := ResidueClassField(R);
  w := Basis(rf);
  pi := UniformizingElement(R);
  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := rf!(p div (-pi^e));
  mu0 := Valuation(e,p)+1;
     y:=PolynomialRing(rf).1;
 root:=Roots(y^(p^(mu0-1)*(p-1))-eps,rf);
 for r in root  do
     return Flat(r[1]);
  end for;
end function;




function residue_system_basis_II(R)

  F := ResidueClassField(R);
  w := Basis(F);
//"w",w;
  c := find_w1(R);
//"c",c;
  max, pos := Maximum([c[i]:i in [1..#c]]);
//[w[i]^c[i]: i in [1..#w ]];
  w1 := &+[w[i]*c[i]: i in [1..#w ]];
//"w1",w1;
 if pos ne 1 then
    w[pos] := w[1];
  end if;
  w[1] := w1;

  return [R!w[i] : i in [1..#w]];
end function;


function wstar(R)

  p := Prime(R);
  pi := UniformizingElement(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := -p div pi^e;
  rf := ResidueClassField(R);
  w := Basis(rf);
  rfy := PolynomialRing(rf); y := rfy.1;

  C := CartesianPower([0..p-1],#w);
  for c in C do
    w_star := &+[w[i]*c[i]: i in [1..#w ]];
    h := y^p-rf!eps*y-w_star;
    if IsIrreducible(h) then
      return R!w_star;
    end if;
  end for;
  error "PrincipalUnitGroupGenerators: Fatal error in computation of w_star.";
end function;



function Fe(R)

  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));

  F := [];
  for i := 1 to Floor(p*e/(p-1)) do
    if i mod p ne 0 then
      Append(~F,i);
    end if;
  end for;

  return F;

end function;


function principal_units_generators_I(R)
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: case I";

//p := Prime(R);
  pi := UniformizingElement(R);
  m := Precision(R);

  resy := residue_system_basis(R);
//"resy",resy;

  gens := [];

  F := Fe(R);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Fundamental levels:", F;
//"Fe",F;
  for nu in F do
    if nu lt m then
      for r in resy do
        Append(~gens, 1+r*pi^nu);
      end for;
    end if;
  end for;
//"gens",gens;
  return gens;

end function;

function principal_units_generators_II(R);

  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: case II";

  e := RamificationIndex(R,PrimeRing(R));
  p := Integers()!Prime(R);
  mu0 := Valuation(e,p)+1;
//(e/(p^(mu0-1)*(p-1)));
  e0 := Integers()!(e/(p^(mu0-1)*(p-1)));

  pi := UniformizingElement(R);
  m := Precision(R);

  resy := residue_system_basis_II(R);
//"resy",resy;    
  gens := [];

  F := Fe(R);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Fundamental levels:", F;
  for nu in F do
    if nu lt m then
     for r in resy do
        Append(~gens, 1+r*pi^nu);
      end for;
    end if;
  end for;
  Append(~gens, 1+wstar(R)*pi^(p^mu0*e0));

  return gens;

end function;


function principal_units_generators(R)

  e := RamificationIndex(R,PrimeRing(R));
  p := Prime(R);

  if e mod (p-1) ne 0 or h2_is_isomorphism(R) or Precision(R) lt e/(p-1) then
     gens :=  principal_units_generators_I(R);
  else
     gens := principal_units_generators_II(R);
  end if;

  gens := Reverse(gens);
  //vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Generators:", gens;
  return gens;
end function;


intrinsic CPrincipalUnitGroupGenerators(R::RngPad) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(R);
end intrinsic;

intrinsic CPrincipalUnitGroupGenerators(R::RngPadRes) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(R);
end intrinsic;

intrinsic CPrincipalUnitGroupGenerators(R::FldPad) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(Integers(R));
end intrinsic;


function basis(R)
//{absolute basis of a local ring}

  T := R;
  L := [1];
  repeat
    S := T;
    M := [ [S.1^ex*l: ex in [0..Degree(S)-1]] : l in L];
    L := Flat(M);
    T :=  BaseRing(S);
  until BaseRing(S) eq PrimeRing(S);
  return L;

end function;

///////////////////////CUnitGroupGenerators/////////////////////

function unit_group_generators(R,raw)

  gens := CPrincipalUnitGroupGenerators(R);
  p := Prime(R);
  rf, mrf := ResidueClassField(R);
  rfu, mrfu := UnitGroup(rf);
//"rfu",rfu;
//"pu",pu;
//#rf;
//"hi",((Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  if raw then
    cycgen := R!mrf(mrfu(rfu.1));
  else
    cycgenexp := #rf^(Ceiling(Precision(R)/Valuation(#rf,p)));
    cycgen := (R!mrf(mrfu(rfu.1)))^cycgenexp;
  end if;

  Append(~gens, cycgen);
  //R!mrf(mrfu(rfu.1)));
  vprint PrincipalUnitGroup,4: "UnitGroupGenerators:",gens;

  return gens;

end function;

intrinsic CUnitGroupGenerators(R::RngPad:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local ring R.
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(R)): "The ring must be of finite precision";
  return unit_group_generators(R,Raw);
end intrinsic;

intrinsic CUnitGroupGenerators(R::RngPadRes:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local ring R.
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(R)): "The ring must be of finite precision";
  return unit_group_generators(R,Raw);
end intrinsic;

intrinsic CUnitGroupGenerators(F::FldPad:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local field F.
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(F)): "The field must be of finite precision";
  gens := [UniformizingElement(F)];
  return ([F!g: g in unit_group_generators(Integers(F),Raw)] cat gens);
end intrinsic;




////////////////////////////NormGroup using  CUnitGroupGenerators//////////////////////

intrinsic NormGroup_fast(R::FldPad,m::Map) -> GrpAb, Map
{The norm group of R as a subgroup of the unit group of its base field/ring B; m : UnitGroup(B) -> B, using CUnitGroupGenerators}
//"NormGroup: begin";
  gens := CUnitGroupGenerators(R);
  B := Codomain(m);
    C := R;
    while C ne PrimeField(R) do
        if B cmpeq C then
            break;
        end if;
        C := CoefficientRing(C);
    end while;
  require B cmpeq C :
    "Codomain of argument 2 must be a coefficient ring of argument 1";
  U := Domain(m);
  require Type(U) eq GrpAb : "Codomain of argument 2 must be a unit group";
  Ugens := [ Norm(g,B)@@m : g in gens];
  S, mS := sub<U | Ugens>;
//"NormGroup: end";
  return S, mS;
end intrinsic;

intrinsic NormGroup_fast(R::RngPad,m::Map) -> GrpAb, Map
{"} //"
//"NormGroup: begin";
  gens := CUnitGroupGenerators(R);
  B := Codomain(m);
    if IsField(B) then
        B := Integers(B);
    end if;
    C := R;
    while C ne PrimeRing(R) do
        if B eq C then
            break;
        end if;
        C := CoefficientRing(C);
    end while;
  require B eq C :
    "Codomain of argument 2 must be a coefficient ring of argument 1";
  U := Domain(m);
  require Type(U) eq GrpAb : "Codomain of argument 2 must be a unit group";
  Ugens := [ Norm(g,B)@@m : g in gens];
  S, mS := sub<U | Ugens>;
//"NormGroup: end";
  return S, mS;
end intrinsic;






////////New Version Of NormEquation////////////////////

function normed_torsion_0(R, b)//->.
//{}
//b:=RingOfIntegers(Parent(b))!b;
p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
//    if b^p^Floor((e/(p-1))) eq 1 then
//Since I am working only for norm equation of RingElt   
   if Type(b) eq FldPadElt then
   gens:=CUnitGroupGenerators(FieldOfFractions(R));
   u,mu:=UnitGroup(FieldOfFractions(Parent(b)));
else
   gens:=CUnitGroupGenerators(RingOfIntegers(R));
   u,mu:=UnitGroup(RingOfIntegers(Parent(b)));
end if;
//   gens:=CUnitGroupGenerators(R);
   // u,mu:=UnitGroup(Parent(b));
   phi:=hom<FreeAbelianGroup(#gens)->u| [Norm(gens[i],Codomain(mu)) @@ mu : i in [1..#gens]]>;
   if not b@@mu in Image(phi) then return false,"Norm fails";
  else

    pre_b:=b @@ mu;
    b_seq:= Eltseq(pre_b @@ phi);
// return &*[gens[i]^b_seq[i]: i in [1..#gens]];
//end if;
return true, &*[gens[i]^b_seq[i]: i in [1..#gens]];

end if;
end function;

intrinsic TorsionNorm(R::RngPad, b::RngPadElt)->RngPadElt
{The norm equation of unit element containing torsion unit}
return normed_torsion_0(R,b);
end intrinsic;
intrinsic TorsionNorm(R::FldPad, b::RngPadElt)->RngPadElt
{The norm equation of unit element containing torsion unit}
return normed_torsion_0(R,b);
end intrinsic;


intrinsic TorsionNorm(R::FldPad, b::FldPadElt)->RngPadElt
{The norm equation of unit element containing torsion unit}
return normed_torsion_0(R,b);
end intrinsic;



/*
function normed_torsion_0(R, b)//->.
//{}
 p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
//    if b^p^Floor((e/(p-1))) eq 1 then
//Since I am working only for norm equation of RingElt    
     gens:=CUnitGroupGenerators(Integers(R));
//  u,mu:=UnitGroup(RingOfIntegers(Parent(b)));
   if Type(b) eq FldPadElt then
   gens:=CUnitGroupGenerators(FieldOfFractions(R));
else
   gens:=CUnitGroupGenerators(RingOfIntegers(R));
   end if;
    u,mu:=UnitGroup(Parent(b));
   phi:=hom<FreeAbelianGroup(#gens)->u| [Norm(gens[i],Codomain(mu)) @@ mu : i in [1..#gens]]>;
   if not b@@mu in Image(phi) then return false;
  else

    pre_b:=b @@ mu;
    b_seq:= Eltseq(pre_b @@ phi);
// return &*[gens[i]^b_seq[i]: i in [1..#gens]];
//end if;
return &*[gens[i]^b_seq[i]: i in [1..#gens]];

end if;
end function;

intrinsic TorsionNorm(R::RngPad, b::RngPadElt)->.
{The norm of torsion unit element}
return normed_torsion_0(R,b);
end intrinsic;
intrinsic TorsionNorm(R::FldPad, b::RngPadElt)->.
{The norm of torsion unit element}
return normed_torsion_0(R,b);
end intrinsic;

intrinsic TorsionNorm(R::FldPad, b::FldPadElt)->.
{The norm of torsion unit element}
return normed_torsion_0(R,b);
end intrinsic;

intrinsic TorsionNorm(R::RngPad, b::FldPadElt)->.
{The norm of torsion unit element}
return normed_torsion_0(R,b);
end intrinsic;

*/

intrinsic myexp(b)->.
{ fast method to compute exponential in Unramified over Ramified to unramified }
   exp := 1 + b;
    term := b;
//for i in [2..Precision(Parent(b))] do
for i in [2..Precision(b)] do
  term *:=b div Parent(b)!i;
  exp +:=term;
   end for;
   return exp;
// return &+[s^i/Factorial(i): i in [0..Precision(R)]];
end intrinsic;


intrinsic MyExp(b)->.
{ fast method to compute exponential in Unramified over Ramified to unramified }
   exp := 1 + b;
    term := b;
//for i in [2..Precision(Parent(b))] do
for i in [2..Precision(b)] do
  term *:=b/i;
  exp +:=term;
   end for;
   return exp;
// return &+[s^i/Factorial(i): i in [0..Precision(R)]];
end intrinsic;


intrinsic Exp_Log_Original(R,b)->.
{ fast method to compute norm equation for higher unit group elements }

repeat
     r:=Random(RingOfIntegers(R));
     until not Trace(r) eq 0 and Valuation(r/Trace(r)*Log(b)) ge Valuation(Log(b));

    s:=r/Trace(r)*Log(b);
      ChangePrecision(~s,Precision(R));
    return Exp(s);
 end intrinsic;   

intrinsic Exp_Log(R,b)->.
{ fast method to compute norm equation for higher unit group elements }
// chqanged on 02,May
//r:=Random(RingOfIntegers(R));

/*PUGG :=CPrincipalUnitGroupGenerators(R);
repeat
  r:= Random(PUGG);
  until not Trace(r) eq 0; 
*/
repeat
     r:=Random(RingOfIntegers(R));
     until not Trace(r) eq 0 and Valuation(r/Trace(r)*Log(b)) ge Valuation(Log(b));

    s:=r/Trace(r)*Log(b);
      ChangePrecision(~s,Precision(R));

exp := 1 + s;
    term := s;
for i in [2..Precision(R)] do
  term *:=s/i;
  exp +:=term;
   end for;

return exp;

 // return &+[s^i/Factorial(i): i in [0..Precision(R)]];

end intrinsic;



function AliNeq(R,b)//->.{}

  if Degree(R, Parent(b)) eq InertiaDegree(R, Parent(b)) and Precision(b) gt 200 then
           return  NormEquation_prec(R, b);
        end if;

// b:=RingOfIntegers(Parent(b))!b;
OR:=RingOfIntegers(R);
 p:=Prime(R);
 e:=RamificationIndex(R,PrimeRing(R));
b:=RingOfIntegers(Parent(b))!b;
//  f,mf:= ResidueClassField(RingOfIntegers(Parent(b)));
if not AbsoluteDegree(Parent(b)) eq AbsoluteDegree(BaseRing(R)) then
   bool,b_norm:=TorsionNorm(R,b);
   return b_norm;
   end if;

   if RamificationDegree(R) eq 1 then
        return Norm_Equation_Unramified(OR,b);
     else
          return Norm_Equation_Ram(OR,b);
       end if;

  end function;


intrinsic Norm_Equation_Ram(R,b)->.{}
 OR:=RingOfIntegers(R);

 p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
//if not Integers(BaseRing(R))!Norm(UniformizingElement(R)) eq Integers(Parent(b))!UniformizingElement(Parent(b)) then
Pi:=UniformizingElement(R);
         bb:=b div Norm(Pi)^Valuation(b);
          ChangePrecision(~bb, Precision(b));
// "we change precision because of the precision loss while dividing";
   // Teich_bb:=teichmueller_lift(R,bb);
   // bbb:=bb div Teich_bb;
//"in ramified extension no teichmueller lift";
if Valuation(bb-1) in [0.. Ceiling((e/(p-1)))] then
        bool,bb_norm:=TorsionNorm(R,bb);
   if  bool eq false then return "Norm fails"; end if;
      else
           bb_norm:=Exp_Log(R,bb);

    end if;
return OR!(bb_norm*UniformizingElement(R)^Valuation(b));

end intrinsic;




intrinsic teichmueller_lift(R,b)->.
{}
  OR:= RingOfIntegers(R);
  if RamificationDegree(R) eq 1 then
    p:=Prime(R);
    //e:=RamificationIndex(R,PrimeRing(R));
  f,mf:= ResidueClassField(RingOfIntegers(Parent(b)));
  _,R_fb:=NormEquation(ResidueClassField(RingOfIntegers(R)),f!b);
  Teich_b:=OR!R_fb^p^(AbsoluteDegree(R));


 /*
 n:=p^Precision(R);
   repeat
        Teich_b1:=R!R_fb^n;
         n:= n*n;
         until true;
 */
 return Teich_b;

  else     return "No Teichmueller Lift" ;
end if;
end intrinsic;

intrinsic Norm_Equation_Unramified(R,b)->.
{Norm in Unramified Extension}
OR:=RingOfIntegers(R);
    p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
    f:=InertiaDegree(R);
    if Valuation(b-1) eq 1 and InertiaDegree(R,PrimeRing(R)) eq AbsoluteDegree(R) then
      //"Here the exp fucntion works well";
      return Exp_Log_Original(R,b);
       end if;

     if not  Valuation(b) in [f*i: i in [0..Precision(R)]] then
    return "No Norm For the Element because of root of uniformizing element R";
else
       i_0:= Valuation(b) div f ;
       b0:=b div Norm(UniformizingElement(R))^i_0;

      Teich_b0:=teichmueller_lift(R,b0);
//bb:=b0 div Norm(Teich_b0);
bb:=b0 div Norm(Teich_b0);
// beacuse of "the division is not exact" failure; 
ChangePrecision(~bb,Precision(Parent(b)));
if Valuation(bb-1) in [0.. Ceiling((e/(p-1)))] or bb/Exp(Log(bb)) ne 1 then
  //if Valuation(bb-1) in [0.. Floor((e/(p-1)))] then
  bool,bb_norm:=TorsionNorm(R,bb);
      assert bool;
      else
         bb_norm:=Exp_Log(R,bb);

   end if;
     end if;
//  return OR!(bb_norm*UniformizingElement(R)^i_0*Teich_b0);
 return bb_norm*UniformizingElement(R)^i_0*Teich_b0;
end intrinsic;



intrinsic ClNormEquation(R::RngPad,b::RngElt) -> RngPadElt {"} //"
 // b in BaseRing(R);

  return AliNeq(R,b);
  end intrinsic;

intrinsic ClNormEquation(R::FldPad,b::RngElt) -> RngPadElt {"} //"
//  b in BaseRing(R);

  return AliNeq(R,b);
  end intrinsic;
intrinsic ClNormEquation(R::FldPad,b::FldPadElt) -> RngPadElt {"} //"
//  b in BaseRing(R);

  return AliNeq(R,b);
  end intrinsic;


intrinsic CANormEquation(R::FldPad,b::RngElt) -> FldPadElt {"} //"
//  b in BaseRing(R);

  //return AliNeq(R,b);
    repeat
     c :=AliNeq(R,b);
  until  Valuation(Norm(c)/b-1) gt 0;

 if Valuation(Norm(c)/b-1) lt Precision(R) then
     b1 := b/Norm(c);
     c1 := AliNeq(R,b1);
     if  Valuation(Norm(c*c1)/b-1) lt Precision(R) then
         b2 := b/Norm(c*c1);
         c2 :=AliNeq(R,b2);
             if Valuation(Norm(c*c1*c2)/b-1) lt Precision(R) then
               b3 := b/Norm(c*c1*c2);
               c3 :=AliNeq(R,b3);
               return c*c1*c2*c3;
               else
               return c*c1*c2;
              end if;
        else
        return c*c1;
      end if;
 else
     return c;
 end if;
end intrinsic;


intrinsic CANormEquation(R::RngPad,b::RngPadElt) -> FldPadElt {"} //"
//  b in BaseRing(R);


//  c :=AliNeq(R,b);

  repeat
     c :=AliNeq(R,b);
  until  Valuation(Norm(c)/b-1) gt 0;

 if Valuation(Norm(c)/b-1) lt Precision(R) then
     b1 := b/Norm(c);
     c1 := AliNeq(R,b1);
     if  Valuation(Norm(c*c1)/b-1) lt Precision(R) then
         b2 := b/Norm(c*c1);
         c2 :=AliNeq(R,b2);
	     if Valuation(Norm(c*c1*c2)/b-1) lt Precision(R) then
               b3 := b/Norm(c*c1*c2);
	       c3 :=AliNeq(R,b3);
	       return c*c1*c2*c3;
	       else
	       return c*c1*c2;
              end if; 
        else 
        return c*c1;
      end if;
 else 
     return c;
  end if;

end intrinsic;



intrinsic NormEquation_prec(N, a)->.{for high precision in unramified extension}
        N := RingOfIntegers(N);
        L := RingOfIntegers(Parent(a));
        a := L!a;
        assert Degree(N, L) eq InertiaDegree(N, L);
        teich := teichmueller_lift(N,a);
        a1 := a div Norm(teich, L);
        iso_index :=  Ceiling(RamificationIndex(L,PrimeRing(L))/( Prime(L)-1))+1;
        ram_ind := RamificationDegree(N, Parent(a));
	n := 2*iso_index;
        if Valuation(a1-1) gt iso_index then
           //return teich*ClNormEquation(N,a);//"note down solution is of a";
           return Norm_Equation_Unramified(N,a);
        else
            if Precision(a) ge 200  then //and  3*iso_index lt Floor(Precision(a)/10) then
                n := 2* iso_index;//Floor(Precision(a)/10);
            end if;
            U, mU := UnitGroup(L:Prec:= n);
            _,b1 := MyNormEquation(N,mU,a1, n*ram_ind + Degree(N));
            aa := Norm(b1) div a1;
            assert Valuation(aa-1) gt iso_index;
            b2 := Exp_Log_Original(N, aa);
          return teich* (b1 div b2);
        end if;
        //Norm_Equation_Unramified(R,b)
end intrinsic;

intrinsic MyNormEquation_prec(N::RngPad, a::RngPadElt)->.
{combining exp log and MyNormEquation to get the result using low precision to MyNormEquation }
        assert InertiaDegree(N,Parent(a)) eq Degree(N, Parent(a));

        ram_ind := RamificationDegree(N, Parent(a));
        L := Parent(a);
        //N := RingOfIntegers(N);

        teich := teichmueller_lift(N,a);// "for high precison this will be solved in unit group";
        a := a div Norm(teich, L);
        iso_index :=  Ceiling(RamificationIndex(L,PrimeRing(L))/( Prime(L)-1))+1;
        if Valuation(a-1) gt iso_index then
           return teich*ClNormEquation(N,a);
        end if;
        n := 2*iso_index;//Floor(Precision(a)/3);
        if Precision(a) gt 150 then // and (iso_index+3) lt Floor(Precision(a)/10) then
           n := iso_index+3;
         end if;
         U, mU := UnitGroup(L:Prec:= n);
         _,b1 := MyNormEquation(N,mU,a, n*ram_ind + Degree(N));
         aa := Norm(b1) div a;
         assert Valuation(aa-1) gt iso_index;
         b2 := ClNormEquation(N, aa);
         if Type(b1) eq RngPadElt and Type(b2) eq RngPadElt then
            return (b1 div b2)*teich;
         else
            return (b1/b2)*teich;
          end if;
end intrinsic;






/////////////////////////////////CUnitGroup////////////////////////////////
//
/*
function unit_group_map_1(R,cycgen,a)
  return cycgen^Eltseq(a)[1];
end function;

function unit_group_disc_log_1(R,mrf,mrfu,b)
  rfurep := mrf(b)@@mrfu;
  return rfurep;
end function;

function unit_group_disc_log(R,cycgen,mrf,mrfu,irfu,mpu,ipu,b)
  assert b in R and Valuation(b) eq 0;
  rfurep := mrf(b)@@mrfu;
//"rfurep",rfurep,Eltseq(rfurep);
  eta := b div cycgen^Eltseq(rfurep)[1];
//"eta",eta;
//"valeta",  Valuation(eta-1);
  purep := eta@@mpu;
  return irfu(rfurep)+ipu(purep);
end function;


function unit_group_map(R,cycgen,prfu,mpu,ppu,a)
  return cycgen^Eltseq(prfu(a))[1]*mpu(ppu(a));
end function;




function  unit_group_ali(R,prec) //-> .
//{The unit group of a local ring or field R}
//"unit group",prec;
  p := Prime(R);
  rf, mrf := ResidueClassField(R);
  rfu, mrfu := UnitGroup(rf);
//"rfu",rfu;
  if prec eq 1 then
    cycgen := (R!mrf(mrfu(rfu.1)));
    group := rfu;
    map := hom<group -> R | a :-> unit_group_map_1(R,cycgen,a),
                            b :-> unit_group_disc_log_1(R,mrf,mrfu,b)>;
    return group, map;
  end if;

  pu, mpu := principal_unit_group(R,prec);
//"pu",pu;
//#rf;
//"hi",((Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  cycgenexp := #rf^(Ceiling(Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  cycgen := (R!mrf(mrfu(rfu.1)))^cycgenexp;
//"cycgen",(mrf(cycgen))@@mrfu;
//"cycgen",cycgen;

  group, irfu, ipu, prfu, ppu := DirectSum(rfu,pu);
  map :=  hom<group -> R | a :-> unit_group_map(R,cycgen,prfu,mpu,ppu,a),
                                  b :-> unit_group_disc_log(R,cycgen,mrf,mrfu,irfu,mpu,ipu,b)>;
  return group, map;
end function;


intrinsic CUnitGroup(R::RngPad:Prec := false) -> GrpAb, Map
{The group of units of R as an Abelian group A and the map A -> R*.}
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group_ali(R,prec);
  return U,m;
end intrinsic;

intrinsic UnitGroup(R::RngPadRes:Prec := false) -> GrpAb, Map
{"} // "
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group_ali(R,prec);
  return U,m;
end intrinsic;

intrinsic CUnitGroup(R::RngPadResExt:Prec := false) -> GrpAb, Map
{"} // "
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group_ali(R,prec);
  return U,m;
end intrinsic;

function unit_group_fld_disc_log(pi,R,map_rng,fg,ifg, iur,b)
  v := Valuation(b);
  b := b/pi^v;
  rng_rep := (R!b)@@map_rng;
  rep := ifg(fg!v)+iur(rng_rep);
  return rep;
end function;

function unit_group_fld_map(pi,map_rng, pfg, pur, a)
  return pi^Eltseq(pfg(a))[1]*map_rng(pur(a));
end function;


function unit_group_fld(L,prec)
  pi := UniformizingElement(L);
  R := Integers(L);
  units_rng, map_rng := unit_group(R,prec);
  fg := FreeAbelianGroup(1);
  group, ifg, iur, pfg, pur := DirectSum(fg, units_rng);
  map :=  hom<group -> L | a :-> unit_group_fld_map(pi,map_rng, pfg, pur, a),
                           b :-> unit_group_fld_disc_log(pi,R,map_rng,fg,ifg, iur,b)>;

  return group, map;
end function;

intrinsic CUnitGroup(L::FldPad: Prec := false) -> GrpAb, Map
{The unit group of the local field L}
  if Prec cmpeq false then
    prec := Precision(L);
    require IsFinite(prec): "Precision of field must be finite if Prec parameter is not set";
  else
    prec := Prec;
  end if;
  group, map :=  unit_group_fld_check(L, prec);
  return group, map;
end intrinsic;





function principal_unit_group(R, prec)
//{The group of principal units of R as an Abelian group G and the map G -> R*}
  //"principal_unit_group",prec;
  S := R;
  // S := ChangePrecision(R,Maximum(Precision(R),prec+Ceiling(prec/10)));
  // beware of precision loss in log and exp
  Z := Integers();
  Zp := ChangePrecision(PrimeRing(R),2*Precision(PrimeRing(R)));
  //Zp := ChangePrecision(PrimeRing(R),1+Precision(PrimeRing(R)));
  //Zp := PrimeRing(R);
  p := Prime(R);
  f := InertiaDegree(R,PrimeRing(R));
  e := RamificationIndex(R,PrimeRing(R));
  //Precision(S);
  punits := principal_unit_group_quad(S, prec);
  //"punits done";
  purank := #punits`generators;
  ///////////////////////////////////////////////////////////////
  // determine which generators will be needed for this precision
  gens := principal_units_generators(S);
  F :=  Fe(S);
  fund_levs := [f : f in F | f lt prec];
  if #gens gt #F*f and p*e/(p-1) lt prec then
    // case II and high precision
    nrgens := f*#F+1;
  else
    nrgens := f*#fund_levs;
  end if;
  gens := Reverse(Reverse(gens)[1..nrgens]);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators:",gens;
  ///////////////////////////////////////////////////////////////
  //"gens",#gens,gens;
  //"rels", punits`relations;
  //"computing gens_reps";
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup: computing relations";
  gens_reps := [principal_unit_group_quad_disc_log(punits,gens[i]): i in [1..#gens]];

  //CF: careful: the relations are incomplete - they include
  //contributions at the units (everything coprime to p) that need
  //removed. My guess is that this is due to the use of Integers() and
  //Rationals() in the principal_unit_group_quad function instead of
  //the p-adics.
  //So we remove the spurious parts here...
  H := FreeAbelianGroup(#punits`generators);
  H, mH := quo<H|RowSequence(punits`relations)>;
  G := FreeAbelianGroup(#gens);
  h := hom<G -> H | [mH(Domain(mH)!x) : x in gens_reps]>;
  assert IsSurjective(h);
  q, mq := quo<G|Kernel(h)>;
  hq := p^Valuation(#q, p);
q, mmq := quo<q|hq*q>;
  mq := mq*mmq;

  ff := function(y)
    y := Domain(mH)!principal_unit_group_quad_disc_log(punits, y);
    y := y@mH;
    y := y@@h;
    y := y@mq;
    return y;
  end function;
  gf := function(x)
    return PowerProduct(gens, Eltseq(x@@mq));
  end function;


 return q, map<q -> R | x:->gf(x),
                         y:-> ff(y)>;


E_seq := [];

 j := 0;
  if #gens ne Rank(gens_reps_HNF) then
    error "PrincipalUnitGroup: ERROR, insufficient precision.";
  end if;

  for i in [1..#gens] do // we need a matrix E of full rank
    j+:=1;               // which contains the rows of gens_reps
    while gens_reps_HNF[i][j] eq 0 do
      newline := [0 : l in [1..purank]];
      newline[j] := 1;
      Append(~E_seq, newline);
      j +:=1;
    end while;
  end for;
  for i in [j+1..purank] do
    newline := [0 : l in [1..purank]];
    newline[i] := 1;
    Append(~E_seq, newline);
  end for;
  E_seq cat:= gens_reps;
  //"E_seq",E_seq;
  E := Matrix(Zp ,E_seq);
  //E := Matrix(Z ,E_seq);
  //"E",E;
  ZM :=  MatrixAlgebra(Z,#E_seq);
  ZpM :=  MatrixAlgebra(Zp,#E_seq);
  QM :=  MatrixAlgebra(Rationals(),#E_seq);
  E_hnf, E_trans := HermiteForm(E);
  E_inv := E_trans;
  new_rels := ZM!HermiteForm(((ZpM!punits`relations)*E_inv));

  group_rels := RowSequence(Submatrix(new_rels,purank-#gens+1,purank-#gens+1,#gens,#gens));
  assert Determinant(Matrix(group_rels)) ne 0;
  freegroup := FreeAbelianGroup(#gens);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroup: relations:",group_rels;
  group, mgroup := quo<freegroup | group_rels>;
  punits`group := group;
  punits`basis_generators := [];
  for i in [1..#Generators(group)] do
    ex := Eltseq(group.i@@mgroup);
    Append(~punits`basis_generators,&*[ gens[i]^ex[i]:i in [1..#gens]]);
  end for;

  map :=  hom<punits`group -> S | a :-> principal_unit_embedding(S, punits, a),
                                  b :-> principal_unit_group_disc_log
                                        (Zp, E_inv, new_rels, freegroup, punits, mgroup, S!b)>;

  if IsVerbose("PrincipalUnitGroup",3) then

 vprint PrincipalUnitGroup,3:
           "PrincipalUnitGroup: -- testing discrete logarithm...";
    if not &and([map(group.i)@@map eq group.i:i in [1..#Generators(group)]]) then
[<group.i,map(group.i)@@map>:i in [1..#Generators(group)]];
//S;
      error "PrincipalUnitGroup: -- failed, aborting...";
    else
        vprint PrincipalUnitGroup,3:  "PrincipalUnitGroup: -- passed";
    end if;
  end if;

  return group,map;

function principal_unit_embedding(R, punits, rep)
  L := Eltseq(rep);
//"L",L;
//"hoch4",#L;
  return R!&*[punits`basis_generators[i]^L[i]: i in [1..#L]];
//[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//&*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//R!&*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//return &*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
end function;





function principal_unit_group_quad(R,prec) //-> .,.
//{the group of principal units of R together with a map}


  PUNITS := recformat<
            R,              // valuation ring
            n,              // absolute degree of R over Qp
            basis,          // absolute basis of the valuation ring
            prec,           // (pi^prec) is the modulus
            AA,             // list of powers of the representation matrix of (pi)
            AA_inv,         // list of the inverses
            AA_exps,        // AA[i] = (pi)^AA_exps[i]
            level_gens,     // generators
            level_rels,     // step_rels[s] := AA[s+1]*AA_inv[s]
            generators,     // list of generators
            relations,      // relation matrix
            basis_generators,//
            P_elts,
            quadlog,
            quadlogexp,
            group           // principal units as an abelian group
            >;
//prec;
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup: using precision",prec;
  vprintf PrincipalUnitGroup,3: "PrincipalUnitGroup: initializing";
  n := Degree(R,PrimeRing(R));
  e := RamificationIndex(R,PrimeRing(R));
  p := Prime(R);
  QM := MatrixAlgebra(Rationals(),n);
  ZM := MatrixAlgebra(Integers(),n);
  punits := rec<PUNITS| R := R, n := n, basis := basis(R), prec := prec>;

  if true or (p eq 2 or prec eq Precision(R)) then
    // CF: SWITCH HERE 
    logmin := prec; // do not use logarithmic method, there is a bug in the 2-adic log
    // see above example for a p=5 problem as well.
  else
    logmin := 1+Floor(e/(p-1));
  end if;
  l:=1; ls:=0;
  vprintf PrincipalUnitGroup,3: " %o",l;
  PI := pi_rep_mat(R);
  AA := PI;
  punits`AA := [AA];
  punits`AA_inv := [(QM!AA)^-1];
  punits`AA_exps := [1];
  punits`P_elts := [];

//"logmin",logmin;
//while l ne m do
  while l lt Minimum(logmin,prec) do
    ls := ls+1;
    l := Minimum(2^ls,prec);
//"l",l;
    vprintf PrincipalUnitGroup,3: " %o",l;
    AA := PI^l;
    Append(~punits`AA, AA);
    Append(~punits`AA_inv, (QM!AA)^-1);
    Append(~punits`AA_exps, l);
  end while;
  punits`quadlogexp := ls+1;   // up to level quadlog we use the quadratic method
  punits`quadlog := Minimum(2^ls,prec);    // for higher levels the p-adic log/exp
  if l ne prec then
    vprintf PrincipalUnitGroup,3: " finally: %o",prec;
    AA := PI^prec;
    Append(~punits`AA, AA);
    Append(~punits`AA_inv, (QM!AA)^-1);
    Append(~punits`AA_exps, prec);
  end if;

  vprintf PrincipalUnitGroup,3: "\n";
//"AA",punits`AA;
//"AA",punits`AA_exps;

  ////////////////////////////////////////////////////////////
  // if quadlog=1: generators and relations of 1+(pi)/1+(pi^prec)
  ////////////////////////////////////////////////////////////
  if punits`quadlog eq 1 then
    k := 1; s := 1; // k=2^(s-1)
    l := Minimum(2,prec); t := 1;
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- p-adic log method";
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels 1 to",prec;
    punits`level_gens :=
        [ [Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]):j in [1..n]] ];
    punits`generators := punits`level_gens[1];
    punits`level_rels := [HermiteForm(ZM!(punits`AA_inv[s]*punits`AA[s+1]))];
    punits`relations := punits`level_rels[1];
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- done";
    return punits;
  end if;
  ////////////////////////////////////////////////////
  // generators and relations of 1+(pi)/1+(pi^2)
  ////////////////////////////////////////////////////
  k := 1; s := 1; // k=2^(s-1)
  l := Minimum(2,prec); t := 1;
  vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- quadratic method";
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels 1 to 2";
  punits`level_gens :=
        [ [1+&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]:j in [1..n]] ];
  punits`generators := punits`level_gens[1];
  special_hnf := function(A, pr)
    B := VerticalJoin(A, p^pr*IdentityMatrix(Integers(), Ncols(A)));
    B := HermiteForm(B);
    B := Submatrix(B, 1, 1, Rank(B), Ncols(B));
    return B;
  end function;
  punits`level_rels := [special_hnf(punits`AA[s], prec)];
  punits`relations := punits`level_rels[1];
  //////////////////////////////////////////////////////
  // generators and relations of 1+(pi^2)/1+(pi^quadlog)
  //////////////////////////////////////////////////////
  k := 2; s := 2; // k=2^(s-1)
  while l lt Minimum(punits`quadlog,prec) do

  //"M:",punits`relations;
//"g:",punits`generators;
    l := Minimum(2^s,prec);
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels",k,"to",l;
    ///////////////////////////////////////////////////
    // generators and relations of 1+(pi^k)/1+(pi^l)
    ///////////////////////////////////////////////////
    Append(~punits`level_rels,special_hnf(ZM!(punits`AA_inv[s]*punits`AA[s+1]), prec));
    h := [1+&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]:j in [1..n]];
    Append(~punits`level_gens,h);
    punits`P_elts cat:= [1: i in [1..n]];
    punits`P_elts := [ punits`P_elts[i]*
                       PowerProduct([punits`generators[(s-2)*n+j]:j in [1..n] ],
                                    [punits`relations[i][(s-2)*n+j]:j in [1..n]])
                       : i in [1..#punits`generators]];
    P := [ principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i])
          : i in [1..#punits`generators]];
    punits`generators := Flat([punits`generators,h]);
    dim := NumberOfRows(punits`relations);
    new := IdentityMatrix(Integers(),dim+n);
    InsertBlock(~new,punits`relations,1,1);
    InsertBlock(~new,-Matrix(P),1,dim+1);
    InsertBlock(~new,punits`level_rels[s],dim+1,dim+1);
    punits`relations := new;
    k := l; s := s+1;
  end while;
  //vprint PrincipalUnitGroup,4: "PrincipalUnitGroup: Generators:",punits`generators;
  //////////////////////////////////////////////////////
  // generators and relations of 1+(pi^quadlog)/1+(pi^prec)
  //////////////////////////////////////////////////////
  if punits`quadlog lt prec then
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- p-adic log method";
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels",punits`quadlog,"to",prec;
//2^(s-1),"=",punits`quadlog,"=",punits`AA_exps[s];
    Append(~punits`level_rels,HermiteForm(ZM!(punits`AA_inv[s]*punits`AA[s+1])));
    h := [];
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    taking exps";
    for j in [1..n] do
      Append(~h, Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]));
      vprint PrincipalUnitGroup,3: j;
    end for;
    //h := [Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]):j in [1..n]];
    Append(~punits`level_gens,h);
    punits`P_elts cat:= [1: i in [1..n]];
    //vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    power products";
    //

    punits`P_elts := [ punits`P_elts[i]*
                     PowerProduct([punits`generators[(s-2)*n+j]:j in [1..n] ],
                                  [punits`relations[i][(s-2)*n+j]:j in [1..n]])
                     : i in [1..#punits`generators]];
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    taking logs";
    P :=[];
    for i in  [1..#punits`generators] do
      Append(~P, principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i]));
      vprint PrincipalUnitGroup,3: i;
    //P := [ principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i])
    //   : i in [1..#punits`generators]];
    end for;
    punits`generators := Flat([punits`generators,h]);
    dim := NumberOfRows(punits`relations);
    new := IdentityMatrix(Integers(),dim+n);
    InsertBlock(~new,punits`relations,1,1);
    InsertBlock(~new,-Matrix(P),1,dim+1);
    InsertBlock(~new,punits`level_rels[s],dim+1,dim+1);
    punits`relations := new;
//"M:",punits`relations;
//"g:",punits`generators;
  end if;
  vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- done";
  return punits;

end function;

*/

/*

intrinsic Exp_Log(R,b)->.
{ fast method to compute norm equation }
repeat
  r:= Random(RingOfIntegers(R));
  until not Trace(r) eq 0;
    s:=r/Trace(r)*Log(b);
      ChangePrecision(~s,Precision(R));
return MyExp(s);
//return &+[s^i/Factorial(i): i in [0..Precision(R)]];

end intrinsic;

function Solve_It(R,b)  // UsingExpLog for all type of extension
 p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
  if Valuation(b-1) in [1.. Floor((e/(p-1)))] then
  return  true,TorsionNorm(R,b);
  end if;

if  Valuation(b) eq 0 then
  if ResidueClassField(RingOfIntegers(Parent(b)))!b eq 1 then

              tu:=b div Exp(Log(b));
              // to find torsion unit;
    if  tu eq 1  and AbsoluteDegree(Parent(b)) eq AbsoluteDegree(BaseRing(R)) then

           b_norm:= Exp_Log(R,b);
 else
         b_norm:=TorsionNorm(R,b);
   // CP:=CPrincipalUnitGroupGenerators(R);
   //r:=[x: x in CP| not Trace(x) eq 0][1];
      end if;
      return true, b_norm;
else
     return true, TorsionNorm(R,b);

end if;
end if;

 if Valuation(b) gt 0 then
 if not Type(Parent(b)) eq Type(R) then
   return "Convert the type of Parent(b)as of type R and proceed again";
//end if;

 else if not InertiaDegree(R,Parent(b)) eq 1 then
        return true, Norm_Equation_Unramified(R,b);

      else if not Integers(BaseRing(R))!Norm(UniformizingElement(R)) eq Integers(Parent(b))!UniformizingElement(Parent(b)) then
       return false,"No norm for this element ";
    else
         bb:=b div Norm(UniformizingElement(R))^Valuation(b);
      ChangePrecision(~bb, Precision(b));
// "we change precision because of the precision loss while dividing";    
      if Valuation(bb-1) in [0.. Floor((e/(p-1)))] then
         bb_norm:=TorsionNorm(R,bb);
       else
           bb_norm:=Exp_Log(R,bb);
//         r:= Random(RingOfIntegers(R));
  //       s:=r/Trace(r)*Log(bb);
    //     ChangePrecision(~s,Precision(R));
       //  bb_norm:=&+[s^i/Factorial(i): i in [0..Precision(R)]];

    end if;
    return true, bb_norm*UniformizingElement(R)^Valuation(b);
 end if;
 end if;
end if;
end if;

//if Valuation(b) gt 0 and InertiaDegree(R,Parent(b)) gt 1 then
  //return Norm_Equation_Unramified(R,b);
 // end if;


end function;


////////////NormEquation over unramified Extension////////////
intrinsic Norm_Equation_Unramified(R,b)->.
{Norm in Unramified Extension}
    p:=Prime(R);
    e:=RamificationIndex(R,PrimeRing(R));
    f:=InertiaDegree(R,Parent(b));

     if not  Valuation(b) in [f*i: i in [0..Precision(R)]] then
    return "No Norm For the Element because of root of uniformizing element R";
else
       i_0:= Valuation(b) div f ;
       bb:=b div Norm(UniformizingElement(R))^i_0;
      if Valuation(bb-1) in [1.. Floor((e/(p-1)))] then
      bb_norm:=TorsionNorm(R,bb);
      else
           bb_norm:=Exp_Log(R,bb);

   end if;
  // return bb_norm*UniformizingElement(R)^i_0;
  // else
    //      return "No Norm For the Element";
     end if;
  return bb_norm*UniformizingElement(R)^i_0;
end intrinsic;



intrinsic ClNormEquation(R::RngPad,b::RngElt) -> BoolElt, RngElt
{}
 // b in BaseRing(R);

  return Solve_It(R,b);
  end intrinsic;

intrinsic ClNormEquation(R::FldPad,b::RngElt) -> BoolElt, RngElt
{} 
//  b in BaseRing(R);

  return Solve_It(R,b);
  end intrinsic;

*/




