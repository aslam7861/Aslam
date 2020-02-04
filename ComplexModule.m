////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// "solves relative_completion, gfcUndecomposed_relative_check";


GFCcomp := recformat<
    CohL : ModCoho,         // cohomology group
    f1CL : Map,             //   with map
    gfcId : ModTupRngElt,   // global fundamental class
    CL : GrpAb,             // module C_L
    psiCL : Map,            //   with G-action
    qCL : Map,              // projection J_L-->>C_L
    primes : SeqEnum,       // set of primes
    US : GrpAb,             // S-Units w.r.t primes
    mUS : Map,              //   with map to L
    kappaInf : SeqEnum,     // inclusions US --> ind^G US
    RepInf : SeqEnum,       //   with corresponding system of representatives
    inclJL : SeqEnum,       // inclusions J_{L_v} --> J_L
    inclUSJL : Map,
    lat : Any,              // lattice
    theta : SeqEnum        // lattice generators
>;

intrinsic trivialSClassNumberPrimes(L::FldNum : primes := []) -> SeqEnum
{ Compute a sequence of primes such that the S-class number of
  all subfields of L is trivial. Optionally specify a set of primes
  which will be included in S. }
    //print "compute subfields";
    subL := Subfields(L);
    vprintf GFC, 2: "%o subfields ", #subL;
    for sub in subL do
        vprintf GFC, 2: ".";
        F := sub[1];
        //print F;
        //print "compute class group";
        CG, m := ClassGroup(F: Bound := BachBound(F));
        //print "compute S";
        S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);
        CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        while #CGmod gt 1 do
            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            // q muss nicht prim sein!
            //S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            S cat:= &cat([[Ideal(x[1]) : x in Decomposition(F,p[1])] : p in Factorization(q)]);
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
        primes := Sort(Setseq({Generator(s meet Integers()) : s in S}));
        //print primes;
    end for;
    vprintf GFC, 2: " done.";
    
    return primes;
end intrinsic;


intrinsic remark_sunit(K,S,mUS,act )->.{Torsion free module, b,  basis elements, sigma-action,  }
/*
Z :=Integers();
ZK :=MaximalOrder(K);
//Factorisation(Discriminant(ZK));
G, _, mG := AutomorphismGroup(K);
Gv :=DecompositionGroup(InfinitePlaces(K)[1]);
s := mG(Gv.1);
//fac := Factorisation(Discriminant(ZK));
S := [x[1] : x in Factorisation(Discriminant(ZK)*ZK)];
U, mU := SUnitGroup(S);*/
//K:=Domain(s);
US := Domain(mUS);
q, mq := quo<US|US.1>;
//hh := SUnitAction(mUS, [s], S);

h := hom<q -> q | [q.i @@ mq @ act @mq : i in [1..Ngens(q)]]>;

MM:=Matrix([Eltseq(h(q.i)) : i in [1..Ngens(q)]]);
M := GModule(DecompositionGroup(InfinitePlaces(K)[1]), [MM]);
u :=IndecomposableSummands(M);
i := hom<q -> q | [h(q.i) - q.i : i in [1..Ngens(q)]]>;
//[h(y) eq y where y := q!Eltseq(M!x.1) : x in u];
j := hom<q -> q | [q.i + h(q.i) : i in [1..Ngens(q)]]>;
k :=Kernel(j);
//restriction map on k
ik := hom<k -> k | [h(k.i) - k.i : i in [1..Ngens(k)]]>;
X,mX :=quo<q|k>;
x,mx :=sub<q|[X.i@@mX: i in [1..Ngens(X)]]>;
assert #quo<q|k,x> eq 1;
assert #(k meet x) eq 1;
m :=Image(i);
Q,mQ :=quo<m|Image(ik)>;
phi := hom<x->Q|[x.j @i @ mQ: j in [1..Ngens(x)]]>;
assert IsSurjective(phi);

A :=Matrix([Eltseq(x.i@phi): i in [1.. Ngens(x)]]);
A :=Matrix(GF(2),A);
a1,a2,a3 :=SmithForm(A);
a2z :=Matrix(Integers(),a2);
assert Determinant(a2z) in {1,-1};
xgen := [x!Eltseq(a2z[j]): j in [1..Ngens(x)] ];
//[phi(xgen[j]): j in [1..#xgen]];
Lmd := [(xgen[j]@i-(phi(xgen[j]))@@mQ)@@ik : j in [1..Ngens(Q)]];
//Lmd := [xgen[j]@i-(phi(xgen[j]))@@mQ : j in [1..Ngens(Q)]];
  for j in [Ngens(Q)+1..Ngens(x)] do
    Append(~Lmd, xgen[j]@i@@ik);
  end for;
Y :=[xgen[j]-Lmd[j] : j in [1..#xgen]];
assert #quo<q|[k.i: i in [1..Ngens(k)]],Y> eq 1;
/*V:=[q!k.i: i in [1..Ngens(k)]];
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
   for y in Y do
     Append(~V,y);
   end for;
 */

// v_act := SUnitAction(mUS,s,S);
 Y_b :=[xgen[j]-Lmd[j] : j in [1..Ngens(k)]];
 Y_a := [xgen[j]-Lmd[j] : j in [Ngens(k)+1 .. #xgen]];
//vv:=Y[Ngens(k)+1..#Y];
inv := [x:x in Y_a| act(x@@mq) - x@@mq eq US!0];
 vv := [x: x in Y_a| x notin inv];
  for x in inv do
     Append(~vv,x);
  end for;

   for i in [1..Ngens(k)] do
    Append(~vv, q!k.i);
    Append(~vv, Y[i]);
    end for;
  assert #quo<q|vv> eq 1;
return q,mq,Ngens(k),vv,h;
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
end intrinsic;



/*
intrinsic remark_sunit(S,U,mU,s)->.{Torsion free module, map -> Tor_US,b,  basis elements, sigma-action }
K:=Domain(s);
q, mq := quo<U|U.1>;
hh := SUnitAction(mU, [s], S);
h := hom<q -> q | [q.i @@ mq @ hh[1] @mq : i in [1..Ngens(q)]]>;

MM:=Matrix([Eltseq(h(q.i)) : i in [1..Ngens(q)]]);
M := GModule(DecompositionGroup(InfinitePlaces(K)[1]), [MM]);
u :=IndecomposableSummands(M);
i := hom<q -> q | [h(q.i) - q.i : i in [1..Ngens(q)]]>;
//[h(y) eq y where y := q!Eltseq(M!x.1) : x in u];
j := hom<q -> q | [q.i + h(q.i) : i in [1..Ngens(q)]]>;
k :=Kernel(j);
ik := hom<k -> k | [h(k.i) - k.i : i in [1..Ngens(k)]]>;
X,mX :=quo<q|k>;
x,mx :=sub<q|[X.i@@mX: i in [1..Ngens(X)]]>;
assert #quo<q|k,x> eq 1;
assert #(k meet x) eq 1;
m :=Image(i);
Q,mQ :=quo<m|Image(ik)>;
phi := hom<x->Q|[x.j @i @ mQ: j in [1..Ngens(x)]]>;
assert IsSurjective(phi);
A :=Matrix([Eltseq(x.i@phi): i in [1.. Ngens(x)]]);
A :=Matrix(GF(2),A);
a1,a2,a3 :=SmithForm(A);
a2z :=Matrix(Integers(),a2);
assert Determinant(a2z) in {1,-1};
xgen := [x!Eltseq(a2z[j]): j in [1..Ngens(x)] ];
//[phi(xgen[j]): j in [1..#xgen]];
//Lmd := [xgen[j]@i-(phi(xgen[j]))@@mQ : j in [1..Ngens(Q)]];
Lmd := [(xgen[j]@i-(phi(xgen[j]))@@mQ)@@ik : j in [1..Ngens(Q)]];
  for j in [Ngens(Q)+1..Ngens(x)] do
      Append(~Lmd, xgen[j]@i@@ik);
        end for;
	Y :=[xgen[j]-Lmd[j] : j in [1..#xgen]];
	assert #quo<q|[k.i: i in [1..Ngens(k)]],Y> eq 1;
	
  V:= Y[Ngens(k)+1..#Y];
  for i in [1..Ngens(k)] do
     Append(~V,q!k.i);
     Append(~V,Y[i]);
     end for;
     
return q,mq,Ngens(k),V,h;          
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
end intrinsic;

*/

intrinsic free_abelian_group_check(US,b)->.
{......}
   a:=Ngens(US)-1-2*b; 
   if a gt 0 then
     n:=2*b+ 2*a-1;
     else
     n:=2*b;
 end if;
     w:=[* Order(US.1) *];
   for i in [1..n ] do
     Append(~w,0);
   end for;
   w:=[w[i]: i in [1..#w]];
  return  AbelianGroup(w);
end intrinsic;


intrinsic action_matrix(W::GrpAb, A::SeqEnum, a:: RngIntElt, b::RngIntElt)->AlgMatElt
{Computes the action matrix required from US-> W_v}
   assert 2+2*(a-1)+2*b eq Ngens(W);
      M := [];
      for i in [1..2] do
	    Append(~M, Eltseq(A[i]));
      end for;	    
     //for i in [1..a] do
     for i in [1..a-1] do
          Append(~M, Eltseq(W.(2*i+2)));
          Append(~M, Eltseq(W.(2*i+1)));
      end for;
  c := 2+2*(a-1);
  //c := 2+2*(a-1);     
       for i in [1..b] do
           Append(~M, Eltseq(W.(2*i+c)));
           Append(~M, Eltseq(W.(2*i+c-1)));
       end for;
  return  Matrix(M);
end intrinsic;  


/*
intrinsic psi_check(S,US,mUS,Gen,s,b)->.{returns the image of map psi from direct sum to US such that psi is isomorphism}
 act := SUnitAction(mUS, s,S);
 v:=[Gen[1], US.1+Gen[2]];
 T := sub<US|US.1>;
 iT:=hom<T->T|[act(T.i)-T.i : i in [1..Ngens(T)]]>;
 a:=Ngens(US)-1-2*b;
 for i in [2..a] do
   t_i := Gen[i+1]@act -Gen[i+1];
  if t_i eq US!0 then
   Append(~v, Gen[i+1]);
 else if IsSquare(t_i@mUS) eq false then
     eta_i :=(US.1-t_i)@@iT;
     Append(~v, Gen[1+i]+eta_i -v[2]);
     else eta_i := t_i@@iT;
     Append(~v, Gen[1+i]+eta_i -v[2]);
     end if;
     end if;
  end for;

for i in [a+2..#Gen] do
  Append(~v, Gen[i]);
  end for;
  return v;

  end intrinsic;



intrinsic psi_check(S,US,mUS,Gen,s,b)->.{}
 act := SUnitAction(mUS, s,S);
v:=[Gen[1], Gen[2] @ act];
//v:=[Gen[1], US.1+Gen[2]];
 T := sub<US|US.1>;
 iT:=hom<T->T|[act(T.i)-T.i : i in [1..Ngens(T)]]>;
 a:=Ngens(US)-1-2*b;
v:=[Gen[1] ];
 theta :=(Order(US.1) div 2)*US.1;
 v:=[Gen[1], theta+Gen[2] ];
//v:=[Gen[1], Gen[2]+ theta ];
  for i in [2..a] do
// z2 := Gen[i];
  t_i := Gen[i+1]@act -Gen[i+1];
 if t_i in Image(iT) then
   eta_i :=t_i@@iT;
   z_i :=(Gen[i+1]+eta_i)-v[2];
   if z_i@act -z_i eq US!0 then
     Append(~v,z_i);
     else t_ii :=(z_i@act-z_i);
     if  t_ii in Image(iT) then
        Append(~v,(z_i+ t_ii@@iT -v[2] ));
        else Append(~v, z_i+(theta -t_ii)@@iT -v[2]);
        end if;
       end if;
  else   eta_i := (theta -t_i)@@iT;
     z_i :=(Gen[i+1]+eta_i)-v[2];
         if z_i@act -z_i eq US!0 then
          Append(~v,z_i);
           else t_ii :=(z_i@act-z_i);
            if  t_ii in Image(iT) then
        Append(~v,(z_i+ t_ii@@iT -v[2] ));
        else Append(~v, z_i+(theta -t_ii)@@iT -v[2]);
        end if;
        end if;
end if;
end for;

for i in [a+2..#Gen] do
  Append(~v, Gen[i]);
  end for;
  return v;
 end intrinsic;
*/


intrinsic make_invariant(mUS,z,v,theta,act)->.
{add some torsion unit to convert into totally real number}
US :=Domain(mUS);
//act :=SUnitAction(mUS,s,S);
 T := sub<US|US.1>;
 iT:=hom<T->T|[act(T.i)-T.i : i in [1..Ngens(T)]]>;
 t1 := z@act -z;
if t1 in Image(iT) then
  z1 :=z+t1@@iT-v;
  t2:= z1 @act -z1;
  if t2 in Image(iT) then
    return z1-t2@@iT;
    else eta:= (theta -t2)@@iT;
        return z1-eta;
    end if;
else eta:= (theta -t1)@@iT;
    z1 :=z+eta -v;
  if z1 @act -z1 eq US!0 then
  return z1;
  else t2:= z1 @act -z1;
      if t2 in Image(iT) then
    return z1-t2@@iT;
    else eta:= (theta -t2)@@iT;
        return z1-eta;
    end if;

  end if;
end if;
end intrinsic;


intrinsic psi_check(S,mUS,Gen,act,b)->.{alternative of psi_check}

US := Domain(mUS);
theta :=US.1@act;
//theta :=(Order(US.1) div 2)*US.1;
if IsSquare(theta@mUS) eq true then 
 theta :=(Order(US.1) div 2)*US.1;
 end if;

//theta :=US.1@act;
v:=[Gen[1], theta+Gen[2] ];
a:=Ngens(US)-1-2*b;
//act :=SUnitAction(mUS,s,S);

T := sub<US|US.1>;
 iT:=hom<T->T|[act(T.i)-T.i : i in [1..Ngens(T)]]>;

for i in [2..a] do
  v_i:=make_invariant(mUS,Gen[i+1],v[2],theta,act);
 A_1 :=[x: x in T| (Gen[i+1]-v[2]-x)@act-(Gen[i+1]-v[2]-x) eq US!0];
 A_2 :=[x: x in T| (Gen[i+1]-2*v[2]-x)@act-(Gen[i+1]-2*v[2]-x) eq US!0];
 if v_i @act -v_i eq US!0 then
   Append(~v,v_i);
   // elif A_1 :=[x: x in T| (Gen[i+1]-v[2]-x)@h-(Gen[i+1]-v[2]-x) eq US!0];
    elif #A_1 ge 1 then
       Append(~v,Gen[i+1]-v[2]-A_1[1]);
       elif #A_2 ge 1 then
   Append(~v,Gen[i+1]-2*v[2]-A_2[1]);
 else  Append(~v,v_i);
 end if;
  //if #[x: x in T| (Gen[i+1]-v[2]-x)@h-(Gen[i+1]-v[2]-x) eq US!0] gt 0 then
 // Append(~v,)
  //Append(~v,make_invariant(mUS,Gen[i+1],v[2],theta,act));
  end for;
  for i in [a+2..#Gen] do
  Append(~v, Gen[i]);
  end for;
return v;
end intrinsic;

intrinsic psi_isomorphism(S,mUS,V,act,b)->.{computes the map psi such that Z^(a-1) part is invariant}
US:=Domain(mUS);
a := Ngens(US)-1-2*b;
B := [];
if a lt 2 then
return [US.1,-US.1+V[2]];
else g := Eltseq(V[2]@act)[1] ;
    E1 :=[V[2]];
end if;
gcd :=[g];
for i in [2..a] do
  g:=gcd[i-1];
  ai := Eltseq(V[i+1]@act)[1] ;
  g1, e, f := XGCD(g,ai);
  Append(~gcd,g1);
 /*    if i eq 2 then
         ei := e*V[i]+f*V[i+1];
    //     Append(~B,ei@act);
         Append(~E1,ei);
    else ei := e*E1[i-1]+f*V[i+1];
         Append(~E1,ei);
    end if;*/
    ei := e*E1[i-1]+f*V[i+1];
    Append(~E1,ei);
    z:= -(ai div g1)*E1[i-1] + (g div g1)* V[i+1];
    Append(~B,z);
end for;
A := [US.1, E1[a]@act];
  for x in B do
       Append(~A,x);
  end for;
    for i in [a+2..Ngens(US)] do
        Append(~A,V[i]);
    end for;
return A;
end intrinsic;




intrinsic make_positve(u, mUS)->.{Change the signs of SUnit gruop elements so that i_v(u) is positive where v is ramified infinite place.}

   if Sign(Real(Evaluate(u@mUS, InfinitePlaces(Codomain(mUS))[1]))) eq -1 then
	 return -u;
     else return u;
   end if;
end intrinsic;




intrinsic gfcCompositumComp(L::FldNum, L1::FldNum) -> ModCoho, Map, ModTupRngElt, Rec
{ Given an arbitrary Galois extension L/Q and a cyclic extension L1/Q
  of the same degree, this method computes then global fundamental
  class of L/Q.
}

   // require IsCyclic(L1) and Degree(L) eq Degree(L1) :
     //       "Second number field must be cyclic and of the same degree!";
require IsCyclic(L1):"Second number field must be cyclic";
    t := Cputime();

    vprint GFC, 1: "compute composite field";
    IndentPush();
    vtime GFC, 1: N := OptimizedRepresentation(Compositum(L,L1));
   // assert IsTotallyReal(N);
    ON := RingOfIntegers(N);

    Gamma, _ ,psiN := AutomorphismGroup(N);
    psiN := map< Domain(psiN) -> Codomain(psiN) | x :-> psiN(x^(-1)) >;
    IndentPop();

    OL := RingOfIntegers(L);

   vprint GFC, 1: "compute primes";
    IndentPush();

    primes:=[];
primes := [f[1] : f in Factorization(Discriminant(ON))];
/*  seq := [p :   p in primes | #Decomposition(L1, p) eq 1];
    if #seq eq 0 then
    p0:=findUndecomposedPrime(L1);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;*/
   //  prime:=trivialSclassless(L,L1,N);
   prime:=trivialSClassNumberPrimes(N);
   primes:=&cat[prime,primes];
    set:={x: x in primes};
    primes:=[x: x in set];
     seq := [p :   p in primes | #Decomposition(L1, p) eq 1];
if #seq eq 0 then
    p0:=findUndecomposedPrime(L1);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;
S := &cat([  [Ideal(x[1]) : x in Decomposition(N,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();

    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 1: US, mUS := SUnitGroup(S);
    GammaSeq := [sig : sig in Gamma];
    vtime GFC, 1: sigUS := SUnitAction(mUS, [psiN(sig) : sig in GammaSeq],S);
    psiUS := map< Gamma -> Aut(US) | sig :-> sigUS[Index(GammaSeq,sig)] >;
    // S-units for L
    H := FixedGroup(N,L);
    K := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)  :  i in [1..#Generators(US)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);
    USL := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in K]);

 assert &and([ g @ mUS in L : g in Generators(USL)]);
    IndentPop();

    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JN";
    IndentPush();
    lst := [];
    thetaAll := [];

    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();
        PN := Factorization(p*ON)[1,1];
        piN := UniformizingElement(PN);

        vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PN) eq 1 then
            theta := ON!1;
            m := 0;
        else
            theta, m := lattice(PN, piN, psiN);
            for i in [1..2] do
                theta1, m1 := lattice(PN, piN, psiN);
                if m1 lt m then
                    theta := theta1;
                    m := m1;
                end if;
            end for;
        end if;
        Append(~thetaAll, ON!theta);
        vprint GFC, 2: "Time:", Cputime(t);
 vprint GFC, 2: "compute completion, prec =", m+10;
    
     //vtime GFC, 2: NP, iotaN, psiNP := completion_with_precision(N,PN,psiN, m+10);
      
     NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;

        LIST:=[*NP,iotaN,psiNP*];
       // GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX1(N, PN, psiN,LIST, theta, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        H := FixedGroup(N,L);
        //R := [Gamma!x : x in r] where r := leftCosetRepresentatives(H, H meet GammaP);
        indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(MN, psiMN, Gamma);// : RepSys := R);
        diagN := map< N -> indMN | x :->
            &+([ x @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;

 H := FixedGroup(N,L);
        K := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
        indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);

        assert (N!L.1) @ diagN in indML;
 if p ne p0 then
            // trivial cocycle for this
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
 H := FixedGroup(N,L1);
            C, qC := quo< Gamma | H>;
 psiL1 := map< C -> Aut(L1) | g :->
                hom< L1 -> L1 | L1.1 @ Coercion(L1,N) @ psiN(g @@ qC) @ Coercion(N,L1) > >;

// compute ML1
K := [ Kernel(Transpose(HorizontalJoin(
                Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
                : h in H ]
                where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);

 indML1 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
            psiIndML1 := map< C -> Aut(indML1) |
                sig :-> Coercion(indML1, indMN)*psiIndMN(sig @@ qC)*Coercion(indMN,indML1) >;
 // compute completion of L1
            PL1 := Factorization(p*RingOfIntegers(L1))[1,1];
            //print "completion with sufficient precicion for computations up to precision ", m+10;
            vprint GFC, 2: "compute completion, prec =", m+10;
           
	  // L1P, iotaL1, psiL1P := completion_with_precision(L1,PL1,psiL1, m+10);
     L1P, iotaL1 := Completion(L1, PL1 : Precision := 200);
     psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;


c := CLocalFundamentalClassSerre(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
          c2 := map< car<Gamma,Gamma> -> indMN | x :-> c(x[1]@qC, x[2]@qC) @@ iotaL1 @ Coercion(L1,N) @ diagN>;
            vprint GFC, 2: "test cocycle";
            vtime GFC, 2: assert testCocycleGenerators(c2, psiIndMN );
            c2 := map< Domain(c2) -> Codomain(c2) | x:-> c2(x[2]^(-1), x[1]^(-1)) >;
 end if;
 diagN := mUS*diagN;
        Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *]);
        IndentPop();
    end for;


 // infinite places
    vprint GFC, 1: "modules for infinite places";
     Gv:=DecompositionGroup(InfinitePlaces(N)[1]);
    // s :=psiN(Gv.1);
     sigma_act := psiUS(Gv.1);
      sig_g :=hom<US->US| [sigma_act(US.i)-US.i: i in [1..Ngens(US)]]>;
  

    U0,mU0,b,U0_gen,v_act := remark_sunit(N,S,mUS,sigma_act);
     //New generators for US
      V:=[US.1];
     for i in [1..Ngens(US)-1] do
          Append(~V,U0_gen[i]@@mU0);
     end for;

    vv:= psi_isomorphism(S,mUS,V,sigma_act,b); 
    // for i in [1..2*b] do
      //   Append(~V,U0_gen[i]@@mU0);
    // end for;

   // eta := (US.1- (sigma_act(V[2])-V[2]))@@sig_g;


     W := free_abelian_group_check(US,b);
     ww := [-W.1 ,W.1+W.2];
      a:=Ngens(US)-1-2*b;
 for i in [1..a-1] do
          Append(~ww, W.(2*i+2)+ W.(2*i+1));
    //      Append(~ww, W.(2*i+1));
      end for;
  c := 2+2*(a-1);

       for i in [1..b] do
           Append(~ww, W.(2*i+c-1));
           Append(~ww, W.(2*i+c));
          // Append(~ww, W.(2*i+c-1));
       end for;

/*

     for i in [1..a-1] do 
       Append(~ww, W.(i+2)+W.(i+3));
      end for;
      for j in [1..b] do
      Append(~ww, W.(2*(j-1)+2+2*(a-1)));
      Append(~ww, W.(2*(j-1)+3+2*(a-1)));
      end for;*/
  
     HH :=hom<US->W|ww>;
 /*    V:=[US.1];
     for i in [1..Ngens(US)-2*b-1] do
          Append(~V,U0_gen[2*b+i]@@mU0);
     end for;
     for i in [1..2*b] do 
         Append(~V,U0_gen[i]@@mU0);
     end for;	 */
     // sig_g :=hom<US->US| [sigma_act(US.i)-US.i: i in [1..Ngens(US)]]>;
    // eta := (US.1- (sigma_act(V[2])-V[2]))@@sig_g;
  //   sig_g :=hom<US->US| [sigma_act(US.i)-US.i: i in [1..Ngens(US)]]>;
     //check here the map HH needed or not
    // act :=action_matrix(W,[HH(V[1]@sigma_act),( eta+V[2])@HH],a,b);
  act :=action_matrix(W,[-W.1,W.1+W.2],a,b);
   // act :=action_matrix(W,[US.1@HH,US.1@sigma_act@HH+W.2],a,b);
     psiww := map<W-> W| x:-> W!Eltseq(Matrix([Eltseq(x)])*act)>;
     psiM := map< sub<Gamma | Id(Gamma)> -> Aut(W) | sig :-> hom< W-> W |[W.i : i in[1..#Generators(W)]]> >;
     
     indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(W, psiM, Gamma);
//diagN := map< US -> indMN | x :-> &+([ x @HH @psiww  @ kappaMN[i] : i in [1..#kappaMN] ]) >;
  diagN := map< US -> indMN | x :-> &+([ x @ psiUS(RN[i]^(-1)) @HH @psiww  @ kappaMN[i] : i in [1..#kappaMN] ]) >;
  
//diagN := map< US_Tor -> indMN | x :->&+([ x @ proj @  psiUS(RN[i]^(-1)) @i1 @ kappaMN[i] : i in [1..#kappaMN] ]) >;
  c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;

// Fix-module by H
    H := FixedGroup(N,L);
    K := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
    indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
    assert &and([ x @ diagN in indML : x in Generators(USL)]);

    Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *] );
    IndentPop();

vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    // Finitely generated idele group
    vprint GFC, 1: "compute idele group of N";
    IndentPush();
    JN, inclJN, projJN := DirectSum([o[2] : o in lst]);
    // recompute projections
    vtime GFC, 1: projJN := [ hom< Domain(p) -> Codomain(p) | [ p(JN.i) : i in [1..#Generators(JN)]] >  : p in projJN ];
    //projJN := [ hom< JN -> lst[k,2] |
       // [ Index(seq,i) eq 0 select lst[k,2]!0 else lst[k,2].(Index(seq,i))  : i in [1..#Generators(JN)]]
      //  >
    //    where seq := [Index(Eltseq(inclJN[k](lst[k,2].i)),1) : i in [1..#Generators(lst[k,2])]]
  //      : k in [1..#lst]];

    vtime GFC, 1: actJN := [ hom< JN -> JN |
        [&+( [ JN.j @ projJN[k] @ lst[k,3](sig) @ inclJN[k] : k in [1..#lst]]) : j in [1..#Generators(JN)]]
        > :  sig in GammaSeq];
    psiJN := map< Gamma -> Aut(JN) | sig :-> actJN[ Index(GammaSeq, sig) ] >;

    gamma := map< car<Gamma, Gamma> -> JN | x :-> &+([ x @ lst[i,5] @ inclJN[i]  : i in [1..#lst] ]) >;
    //gammaL := map< Domain(gamma) -> Codomain(gamma) | x :-> gamma(x[2]^(-1), x[1]^(-1)) >;
    //time testCocycleGenerators(gammaL, psiJN);
    IndentPop();

vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of N";
    IndentPush();
     embJN1 := map< US -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst-1]] ) >;
    embJN3 := map< US -> JN | x :->  x @ lst[#lst,4] @ inclJN[#lst] >;
    embJN := map< US -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst]] ) >;
/*   vtime GFC, 1: B := [g @ embJN1 : g in Generators(US)];
       for x in [U0_gen[j]@@mU0 : j in [1..#U0_gen]] do
       Append(~B,x@embJN3);
       end for;
*/
     vtime GFC, 1: B := [g @ embJN : g in vv];
    CN, qCN := quo<JN | B>;
    psiCN := map< Gamma -> Aut(CN) | sig :-> Inverse(qCN)*psiJN(sig)*qCN >;
    //gammaL := map< Domain(gamma) -> CN | x :-> gamma(x[2]^(-1), x[1]^(-1)) @ qCN >;
    //time testCocycleGenerators(gammaL, psiCN);
    IndentPop();
//"till here works well in 260 seconds around for S3":

 vprint GFC, 1: "compute cohomology of N";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCNr := map< Gamma -> Aut(CN) | g :-> psiCN(g^(-1)) >;
    vtime GFC, 1: CohN := CohomologyModule(Gamma, CN, psiCNr);
    f1CN := map< CN -> RSpace(Integers(),Dimension(CohN)) | x:-> Eltseq(x), y:-> CN!Eltseq(y) >;
    // second cohom. group
    //time H2N := CohomologyGroup(CohN,2);
    vtime GFC, 1: H1N := CohomologyGroup(CohN,1);

    gammaC := map< car<Gamma, Gamma> -> CN | x :-> x @ gamma @ qCN >;
    //gfcId := IdentifyTwoCocycle(CohN, func< x | gammaC(x[1],x[2]) @ f1CN >);
    IndentPop();

vprint GFC, 1: "Time for cohomology of N:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    // Cohomology of L
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);

    embLN := map< JL -> JN |
        x :-> &+([ x @ projJL[i] @ Coercion(lst[i,1], lst[i,2]) @ inclJN[i] : i in [1..#lst]]),
        y :-> &+([ y @ projJN[i] @ Coercion(lst[i,2], lst[i,1]) @ inclJL[i] : i in [1..#lst]])
    >;
    G, qG := quo< Gamma | FixedGroup(N,L) >;
    psiJL := map< G -> Aut(JL) | sig :-> embLN * (sig @@ qG @ psiJN) * Inverse(embLN) >;

     vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // changed here too
    vtime GFC, 1: B := [g @ embJN @@ embLN : g in Generators(USL)];
    CL, qCL := quo<JL | B>;

 psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 1: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    vtime GFC, 1: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) | x:-> Eltseq(x), y:-> CL!Eltseq(y) >;
    IndentPop();

 vprint GFC, 1: "Time for all the computation for L:", Cputime(t);
    t := Cputime();

    mUSL := map< USL -> L | x :-> L!(x @ mUS) >;
    inclUSJL := map< USL -> JL | x :-> (US!x) @ diagN @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, //gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US:= USL, mUS := mUSL,
        //kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

     Req:=[* G,qG,Gamma,gammaC,CL,qCL,CN,qCN,embLN,CohL,CohN,H2L,primes,f1CN,thetaAll *];
     list := [* vv, sigma_act, W,HH*];

vprint GFC, 1: "find global fundamental class of L";
  
  IndentPush();

return CohN,f1CN,CohL,list,comp;  
end intrinsic;




intrinsic gfcUndecomposedComp1(L::FldNum, p0::RngIntElt : psiL := 0) -> ModCoho, Map, ModTupRngElt, Rec
{ Computes the global fundamental class for a number field L
  in which the prime p0 is undecomposed.
  Optionally one can pass the Galois action on L as map G->Aut(L/Q).
}

   require #Decomposition(L,p0) eq 1 :
            "Prime must be undecomposed in L!";

    t := Cputime();

    if psiL cmpeq 0 then
        G,_, psiL := AutomorphismGroup(L);
        psiL := map< Domain(psiL) -> Codomain(psiL) | x:-> psiL(x^(-1)) >;
    else
        G := Domain(psiL);
    end if;

    vprint GFC, 1: "compute primes";
    IndentPush();
    primes := {p0} join {x[1] : x in Factorization(Discriminant(RingOfIntegers(L)))};
    subL := Subfields(L);
    for sub in subL do
        F := sub[1];
        CG, m := ClassGroup(F: Bound := BachBound(F));
        S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);

        CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        while #CGmod gt 1 do
            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
        primes := Setseq({Generator(s meet Integers()) : s in S});
    end for;
   //primes := Setseq({Generator(s meet Integers()) : s in S});
   // take extra one prime
   Append(~primes, NextPrime(primes[#primes]));
   S := &cat([  [Ideal(x[1]) : x in Decomposition(L,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();

    OL := RingOfIntegers(L);
    // lat := latticeGlob(L : psi := psiL);


    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 2: US, mUS := SUnitGroup(S);

    sigUS := SUnitAction(mUS, [psiL(sig) : sig in G],S);
    GG := [sig : sig in G];
     psiUS := map< G -> Aut(US) | sig :-> sigUS[Index(GG,sig)] >;
   GammaSeq :=[x: x in G];
   
    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JL";
    IndentPush();
    lst := [];
    thetaAll := [];
    // construct JL
    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();

        PL := Factorization(p*OL)[1,1];
        piL := UniformizingElement(PL);

          vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PL) eq 1 then
            theta := OL!1;
            m := 0;
        else
            theta, m := lattice(PL, piL, psiL);
        end if;
        Append(~thetaAll, OL!theta);
        vprint GFC, 2: "Time:", Cputime(t);

        vprint GFC, 2: "compute completion";
        LP, iotaL := Completion(L, PL : Precision :=2000);
        GP := [g : g in G | &and([  psiL(g)(x) in PL   : x in Generators(PL)]) ];
        GP := sub< G | GP>;
        psiLP := map< GP -> Aut(LP) | g :-> iotaL^(-1) * psiL(g) * iotaL >;
        vprint GFC, 2: "compute module";

	
         LIST := [* LP, iotaL,psiLP *];


        ML, psiML, qML := compute_LPmul_modX1(L, PL, psiL, LIST , theta, m);
        //ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, lat, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        indML, psiIndML, RL, kappaML, projML := inducedModule(ML, psiML, G);
        diagL := map< US -> indML | x :->
           &+([ x @ mUS @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;
       vprint GFC, 2: "compute cocycle";
        if p ne p0 then
            // trivial cocycle for this
            c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
        else

            // cocycle for p
            vtime GFC, 2: brGrp := LocalBrauerGroup(L, p : autMap := psiL, lfc);

            c := TwoCocycle(brGrp`C, brGrp`lfc);
            C := Group(brGrp`C);
            // c := map< car<C,C> -> brGrp`M | x :-> c(x) @@ brGrp`f1 >;
            // c2 := map< Domain(c) -> Codomain(c) | x :-> c(x[2]^(-1), x[1]^(-1)) >;
            //testCocycle(c2, brGrp`actM );

            c2 := map< car<C,C> -> indML | x :-> c(x) @@ brGrp`f1 @@ brGrp`qM @ iotaL @ qML @ kappaML[1] >;
            // pre-compute images
            ll := [x : x in Domain(c2)];
            vtime GFC, 2: llImg := [c2(x) : x in ll];
            c2 := map< Domain(c2) -> Codomain(c2) | x :-> llImg[Index(ll, x)] >;

        end if;
        Append(~lst, [* indML, psiIndML, diagL, c2 *]);
        IndentPop();
    end for;
     
       vprint GFC, 1: "modules for infinite places";
    //assert &and([ IsReal(inf) : inf in InfinitePlaces(L) ]);
     Gv:=DecompositionGroup(InfinitePlaces(L)[1]);
  

//s :=psiL(Gv.1);
  sigma_act := psiUS(Gv.1);
  U0,mU0,b,U0_gen,v_act := remark_sunit(L,S,mUS,sigma_act);
    V:=[US.1];
     for i in [1..Ngens(U0)] do
          Append(~V,U0_gen[i]@@mU0);
         end for;
//     for i in [1..2*b] do
  //       Append(~V,U0_gen[i]@@mU0);
    //     end for;

//eta;
   W := free_abelian_group_check(US,b);
     ww := [W.1 ,-W.1+W.2];
      a:=Ngens(US)-1-2*b;
     for i in [1..a-1] do
         // Append(~ww, W.(2*i+1)+ W.(2*i+2));
         Append(~ww, W.(2*i+1)+ W.(2*i+2));   
     end for;
      c := 2+2*(a-1);
     for i in [1..b] do
           Append(~ww, W.(2*i+c-1));
           Append(~ww, W.(2*i+c));
          // Append(~ww, W.(2*i+c-1));
       end for;
   HH :=hom<US->W|ww>;
 v := psi_isomorphism(S,mUS,V,sigma_act,b);
//To make positivity of Z^(a-1) just multiply by -1 in the gens
//But it is not mapped with mUS otherwise it changes the value
/* vv:=v[1..2];
 a:=Ngens(US)-1-2*b;
 for x in v[3..a+1] do
   //if sentence down not needed
     if Position(v,x) in [3..a+1] then
        Append(~vv, make_positve(x,mUS));
        else Append(~vv,x);
     end if;
 end for;
 for x in v[a+2..Ngens(US)]  do
     Append(~vv,x); 
 end for;*/
assert #quo<US|v> eq 1;  
// HH :=hom<US->W|ww>;
// act :=action_matrix(W,[HH(vv[1]), HH(vv[2])],a,b);
 act :=action_matrix(W,[-W.1, W.1+W.2],a,b);
 psiww := map<W-> W| x:-> W!Eltseq(Matrix([Eltseq(x)])*act)>;
 psiM := map< sub<G | Id(G)> -> Aut(W) | sig :-> hom< W-> W |[W.i : i in[1..#Generators(W)]]> >;
//psiM := map< sub<G | Gv> -> Aut(W) | sig :-> hom< W-> W |[W.i : i in[1..#Generators(W)]]> >;
 ACT :=[psiww*psiww, psiww];
 indML, psiIndML, RL, kappaML, projML := inducedModule(W, psiM, G);
//diagL := map< US -> indML | x :-> &+([ x @ psiUS(RL[i]^(-1)) @HH @ACT[j]   @ kappaML[i] :j in [1..#ACT], i in [1..#kappaML] ]) >;
diagL := map< US -> indML | x :-> &+([ x   @ psiUS(RL[i]^(-1)) @HH @ ACT[j]    @ kappaML[i] :j in [1..#ACT], i in [1..#kappaML] ]) >;
//diagL := map< US -> indML | x :-> &+([ x  @ psiUS(RL[i]^(-1)) @HH @ psiww @ kappaML[i] : i in [1..#kappaML] ]) >;

// "psiwwleaving";
// "for all g in G, g:=RL[i]*b_Gv so g(indML.i)= b_Gv(Rl[i](gamma))  and RL[i](gamma) is going to interchange the coordinates";

 c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
    Append(~lst, [* indML, psiIndML, diagL,  c2 *] );
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    IndentPush();
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);
    // precompute projections
    vtime GFC, 2: projJL2 := [ hom< Domain(p) -> Codomain(p) | [ p(JL.i) : i in [1..#Generators(JL)]] >  : p in projJL ];
    
    vtime GFC, 2: actJL := [ hom< JL -> JL |
        [&+( [ JL.j @ projJL[k] @ lst[k,2](sig) @ inclJL[k] : k in [1..#lst]]) : j in [1..#Generators(JL)]]
        > :  sig in GG];
    psiJL := map< G -> Aut(JL) | sig :-> actJL[ Index(GG, sig) ] >;


     gamma := map< car<G, G> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;


	 IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // diagonal embedding of S-units
    embJL := map< US -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] )  >;
    // factor out S-Units diagonally
    vtime GFC, 2: B := [g @ embJL : g in v];// alternative of "v";
    //vtime GFC, 2: B := [g @ embJL : g in Generators(US)];
    CL, qCL := quo<JL | B>;
    // time homBasis := [ [CL.i @@ qCL @ psiJL(sig) @ qCL : i in [1..#Generators(CL)]] : sig in GG];
    // psiCL := map< G -> Aut(CL) | sig :->
    //     hom< CL -> CL | homBasis[Index(GG, sig)] >
    // >;
    psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();

	 psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 2: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    vtime GFC, 2: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) |
        x:-> Eltseq(x),
        y:-> CL!Eltseq(y)
    >;
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "Identify fundamental class:", Cputime(t);
    gammaC := map< car<G, G> -> CL | x :-> x @ gamma @ qCL >;
    gfcId := IdentifyTwoCocycle(CohL, func< x | gammaC(x[1],x[2]) @ f1CL >);

    inclUSJL := map< US -> JL | x :-> x @ diagL @ inclJL[#inclJL] >;
    list :=[*v, sigma_act, W, HH  *];
    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US := US, mUS := mUS,
        kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

    return CohL, f1CL, gfcId,list;
end intrinsic;

  



















intrinsic gfcUndecomposedComp(L::FldNum, p0::RngIntElt : psiL := 0) -> ModCoho, Map, ModTupRngElt, Rec
{ Computes the global fundamental class for a number field L
  in which the prime p0 is undecomposed.
  Optionally one can pass the Galois action on L as map G->Aut(L/Q).
}
   // require IsTotallyReal(L) :
    //        "Just implemented for totally real fields!";
    require #Decomposition(L,p0) eq 1 :
            "Prime must be undecomposed in L!";

    t := Cputime();

    if psiL cmpeq 0 then
        G,_, psiL := AutomorphismGroup(L);
        psiL := map< Domain(psiL) -> Codomain(psiL) | x:-> psiL(x^(-1)) >;
    else
        G := Domain(psiL);
    end if;

    vprint GFC, 1: "compute primes";
    IndentPush();
    primes := {p0} join {x[1] : x in Factorization(Discriminant(RingOfIntegers(L)))};
    subL := Subfields(L);
    for sub in subL do
        F := sub[1];
        CG, m := ClassGroup(F: Bound := BachBound(F));
        S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);

        CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        while #CGmod gt 1 do
            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
        primes := Setseq({Generator(s meet Integers()) : s in S});
    end for;
    //primes := Setseq({Generator(s meet Integers()) : s in S});
    S := &cat([  [Ideal(x[1]) : x in Decomposition(L,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();

    OL := RingOfIntegers(L);
    // lat := latticeGlob(L : psi := psiL);


    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 2: US, mUS := SUnitGroup(S);
/*
    FT,mFT:=sub<US|TorsionFreeSubgroup(US)>;

   US_Tor,i1,i2,p1,p2:=DirectSum(US,FT);

   proj:=map<US_Tor->US|x:->x@p2@mFT + x@p1>;
  */

  IUS,mIUS:=sub<US|[x: x in Generators(US)][1]>;
   UU,I1,I2,P1,P2:=DirectSum(IUS,IUS);
   pr:=map<UU->US|x:->x@P2@mIUS + x@P1>;
   US_Tor,i1,i2,p1,p2:=DirectSum(US,UU);
  proj:=map<US_Tor->US|x:->x@p2@pr + x@p1>;

  mUS_Tor:=map<US_Tor->FieldOfFractions(OL)| x:->x @ proj @mUS>; 
   sigUS := SUnitAction(mUS_Tor, [psiL(sig) : sig in G],S);
    GG := [sig : sig in G];
 //   vtime GFC, 2: sigUS := SUnitAction(mUS, [psiL(sig) : sig in G],S);
   // psiUS := map< G -> Aut(US) | sig :-> sigUS[Index(GG,sig)] >;
    psiUS := map< G -> Aut(US_Tor) | sig :-> sigUS[Index(GG,sig)] >;
    IndentPop();

    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JL";
    IndentPush();
    lst := [];
    thetaAll := [];
    // construct JL
    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();

        PL := Factorization(p*OL)[1,1];
        piL := UniformizingElement(PL);

        //m := 0;
        //repeat
        //    m := m+1;
        //until &and([b in lat :  b in Generators(PL^m) ]);
        // create lattice for p
        vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PL) eq 1 then
            theta := OL!1;
            m := 0;
        else
            theta, m := lattice(PL, piL, psiL);
        end if;
        Append(~thetaAll, OL!theta);
        vprint GFC, 2: "Time:", Cputime(t);

        vprint GFC, 2: "compute completion";
        LP, iotaL := Completion(L, PL : Precision :=2000);
        GP := [g : g in G | &and([  psiL(g)(x) in PL   : x in Generators(PL)]) ];
        GP := sub< G | GP>;
        psiLP := map< GP -> Aut(LP) | g :-> iotaL^(-1) * psiL(g) * iotaL >;
        vprint GFC, 2: "compute module";
          
	 LIST := [* LP, iotaL,psiLP *];


        ML, psiML, qML := compute_LPmul_modX1(L, PL, psiL, LIST , theta, m);
        //ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, lat, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        indML, psiIndML, RL, kappaML, projML := inducedModule(ML, psiML, G);
      //  diagL := map< US -> indML | x :->
       //     &+([ x @ mUS @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;
     diagL := map< US_Tor -> indML | x :->&+([ x @ mUS_Tor @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >; 
        vprint GFC, 2: "compute cocycle";
        if p ne p0 then
            // trivial cocycle for this
            c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
        else

            // cocycle for p
            vtime GFC, 2: brGrp := LocalBrauerGroup(L, p : autMap := psiL, lfc);

            c := TwoCocycle(brGrp`C, brGrp`lfc);
            C := Group(brGrp`C);
            // c := map< car<C,C> -> brGrp`M | x :-> c(x) @@ brGrp`f1 >;
            // c2 := map< Domain(c) -> Codomain(c) | x :-> c(x[2]^(-1), x[1]^(-1)) >;
            //testCocycle(c2, brGrp`actM );

            c2 := map< car<C,C> -> indML | x :-> c(x) @@ brGrp`f1 @@ brGrp`qM @ iotaL @ qML @ kappaML[1] >;
            // pre-compute images
            ll := [x : x in Domain(c2)];
            vtime GFC, 2: llImg := [c2(x) : x in ll];
            c2 := map< Domain(c2) -> Codomain(c2) | x :-> llImg[Index(ll, x)] >;

        end if;
        Append(~lst, [* indML, psiIndML, diagL, c2 *]);
        IndentPop();
    end for;


    // infinite places
    vprint GFC, 1: "modules for infinite places";
    //assert &and([ IsReal(inf) : inf in InfinitePlaces(L) ]);
     G_inf:=DecompositionGroup(InfinitePlaces(L)[1]);
  /*   FT,mFT:=sub<US|TorsionFreeSubgroup(US)>;
     US_Tor,i1,i2,p1,p2:=DirectSum(US,FT);
     proj:=map<US_Tor->US|x:->x@p2@mFT + x@p1>;
   */
   psiM := map< sub<G | Id(G) > -> Aut(US_Tor) | sig :-> hom< US_Tor -> US_Tor |[US_Tor.i : i in [1..#Generators(US_Tor)]]> >;

//    psiM := map< sub<G | Id(G)> -> Aut(US) | sig :-> hom< US -> US | [US.i : i in [1..#Generators(US)]]> >;
    indML, psiIndML, RL, kappaML, projML := inducedModule(US_Tor, psiM, G);

//    diagL := map< US -> indML | x :->
  //          &+([ x @ psiUS(RL[i]^(-1)) @ kappaML[i] : i in [1..#kappaML] ]) >;
    diagL := map< US_Tor -> indML | x :->  &+([ x @ psiUS(RL[i]^(-1))  @ kappaML[i] : i in [1..#kappaML] ]) >;

    c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
    Append(~lst, [* indML, psiIndML, diagL,  c2 *] );
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    IndentPush();
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);
    // precompute projections
    vtime GFC, 2: projJL2 := [ hom< Domain(p) -> Codomain(p) | [ p(JL.i) : i in [1..#Generators(JL)]] >  : p in projJL ];
    // recomputation of projections using injections much faster
    //projJL := [ hom< JL -> lst[k,1] |
    //    [ Index(seq,i) eq 0 select lst[k,1]!0 else lst[k,1].(Index(seq,i))  : i in [1..#Generators(JL)]]
    //    >
    //    where seq := [Index(Eltseq(inclJL[k](lst[k,1].i)),1) : i in [1..#Generators(lst[k,1])]]
    //    : k in [1..#lst]];

    vtime GFC, 2: actJL := [ hom< JL -> JL |
        [&+( [ JL.j @ projJL[k] @ lst[k,2](sig) @ inclJL[k] : k in [1..#lst]]) : j in [1..#Generators(JL)]]
        > :  sig in GG];
    psiJL := map< G -> Aut(JL) | sig :-> actJL[ Index(GG, sig) ] >;


     gamma := map< car<G, G> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;
    //gfcId := IdentifyTwoCocycle(CohJL, func< x | gamma(x[1],x[2]) @ f1JL >);
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // diagonal embedding of S-units
    embJL := map< US_Tor -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] )  >;
    // factor out S-Units diagonally
    vtime GFC, 2: B := [g @ embJL : g in Generators(US_Tor)];
    CL, qCL := quo<JL | B>;
    // time homBasis := [ [CL.i @@ qCL @ psiJL(sig) @ qCL : i in [1..#Generators(CL)]] : sig in GG];
    // psiCL := map< G -> Aut(CL) | sig :->
    //     hom< CL -> CL | homBasis[Index(GG, sig)] >
    // >;
    psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    
    /*
    //" Rough to check whether Cohomology module exist?";
     i := AbelianInvariants(A);
  if Type(m) eq SeqEnum then
    m := [ Matrix([Eltseq(A.i@j) : i in [1..Ngens(A)]]) : j in m];
  elif Type(m) eq Map  or Type(m) eq UserProgram then
    m := [ Matrix([Eltseq(A.i@m(G.j)) : i in [1..Ngens(A)]]) : j in [1..Ngens(G)]];
  else
    error "argument not supported";
  end if;
   CohomologyModule(G, i, m);

    
    */
    psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 2: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    vtime GFC, 2: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) |
        x:-> Eltseq(x),
        y:-> CL!Eltseq(y)
    >;
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "Identify fundamental class:", Cputime(t);
    gammaC := map< car<G, G> -> CL | x :-> x @ gamma @ qCL >;
    gfcId := IdentifyTwoCocycle(CohL, func< x | gammaC(x[1],x[2]) @ f1CL >);

    inclUSJL := map< US -> JL | x :-> x @ diagL @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US := US, mUS := mUS,
        kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

    return CohL, f1CL, gfcId, comp;
end intrinsic;

function relative_completion1(L, K, p)

 P:=Decomposition(MaximalOrder(K),p)[1,1];
 Kp,mKp:=Completion(MaximalOrder(K),P : Precision:=100);
 Kp1:= ChangePrecision(Kp,100);
f:= DefiningPolynomial(L);
 A:= [x @ mKp: x in Eltseq(f)];
  fp:=Polynomial(A);
//Roots(fp,Kp);
  Lp :=ext<Kp1| fp>;
  // "Ask whether for uniformizing element or primitive element"";
 //pi:=UniformizingElement(Lp);
 mL := hom<L -> Lp | map<K -> Lp| x:-> Lp!mKp(x)>, Lp.1>;
 //mL := hom<L -> Lp | map<K -> Lp| x:-> Lp!mKp(x)>, pi>;
 mL_p:=hom< Lp -> L| x:-> L![(Kp!Kp1!g) @@ mKp : g in Eltseq(x)]>;
mLp:=hom<L->Lp| x:->mL(x), y:->mL_p(y)>;
return Lp,mLp;

end function;

intrinsic relative_completion(L, K, p, precision)->FldPad,Map
{ For L/K the relative extension and K/Q, this computes the completion of L to Lp and gives the map from Abs(L) to Lp. "This works for all prime in relative filed".}
// Here L_abs may be different  so do it in relative only
 L_abs :=AbsoluteField(L);
 //K:= AbsoluteField(K);
 P:= Factorisation(p*MaximalOrder(K))[1,1];
 //P:=Decomposition(K,p)[1,1];
 Kp,mKp:=Completion(K,P : Precision:= precision);
 Kp1:= ChangePrecision(Kp,precision);
mKp:=hom<Domain(mKp)-> Kp1|x:-> Kp1!(x@ mKp), y:-> y@@ mKp >;
f:= DefiningPolynomial(L);
R<y> := PolynomialRing(Kp1);
 A:= [x @ mKp: x in Eltseq(f)];
  fp:=Polynomial(A);
//Roots(fp,Kp);
if IsIrreducible(fp) then
loc:= LocalField(Kp1, fp);
 else loc := LocalField(Kp1, Factorisation(fp)[1,1]);
 end if;
 Lp,mLp:= RamifiedRepresentation(loc);
// "map mLp is isomorphism from loc to Lp";
//  mLp:= hom<L_abs->Lp| x:-> Lp![(z@mKp)@mLp: z in Eltseq(L!x)] ,
  //                 y:->L_abs!(L![(z@@ mLp)@@ mKp: z in Eltseq(y)])    >;

//mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(Evaluate(Polynomial([ z@@ mKp : z in Eltseq(y@@ mLp)]),L.1))>;
mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(Evaluate(Polynomial([ z@@ mKp : z in Eltseq(y@@ mLp)]),L.1))>;
return Lp,mLp;

end intrinsic;

intrinsic relative_completion_check(N,L, K, p, precision)->FldPad,Map
{ N is absolute filed. For L/K the relative extension and K/Q, this computes the completion of L to Lp and gives the map from Abs(L) to Lp. This is the same as relative_completion."This works for all prime in relative filed".}
// Here L_abs may be different  so do it in relative only
 L_abs :=N;
 //K:= AbsoluteField(K);
 P:= Factorisation(p*MaximalOrder(K))[1,1];
 //P:=Decomposition(K,p)[1,1];
 Kp,mKp:=Completion(K,P : Precision:= precision);
 Kp1:= ChangePrecision(Kp,precision);
mKp:=hom<Domain(mKp)-> Kp1|x:-> Kp1!(x@ mKp), y:-> y@@ mKp >;
f:= DefiningPolynomial(L);
R<y> := PolynomialRing(Kp1);
 A:= [x @ mKp: x in Eltseq(f)];
  fp:=Polynomial(A);
//Roots(fp,Kp);
if IsIrreducible(fp) then
loc:= LocalField(Kp1, fp);
 else loc := LocalField(Kp1, Factorisation(fp)[1,1]);
 end if;
 Lp,mLp:= RamifiedRepresentation(loc);
// "map mLp is isomorphism from loc to Lp";
//  mLp:= hom<L_abs->Lp| x:-> Lp![(z@mKp)@mLp: z in Eltseq(L!x)] ,
  //                 y:->L_abs!(L![(z@@ mLp)@@ mKp: z in Eltseq(y)])    >;

//mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(Evaluate(Polynomial([ z@@ mKp : z in Eltseq(y@@ mLp)]),L.1))>;
// "in some case Eltseq can not be coerced so have to add 0";
mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(L!(L_elt([z@@ mKp : z in Eltseq(y@@ mLp)],L)))>;
//mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(Evaluate(Polynomial([ z@@ mKp : z in Eltseq(y@@ mLp)]),L.1))>;

return Lp,mLp;

end intrinsic;





intrinsic relative_completion_check_update(N,L, K, p, precision)->FldPad,Map
{ N is absolute filed. For L/K the relative extension and K/Q, this computes the completion of L to Lp and gives the map from Abs(L) to Lp. This is the same as relative_completion."This works for all prime in relative filed".}
// Here L_abs may be different  so do it in relative only
 L_abs :=N;
 //K:= AbsoluteField(K);
 P:= Factorisation(p*MaximalOrder(K))[1,1];
 //P:=Decomposition(K,p)[1,1];
 Kp,mKp:=Completion(K,P : Precision:= precision);
 Kp1:= ChangePrecision(Kp,precision);
mKp:=hom<Domain(mKp)-> Kp1|x:-> Kp1!(x@ mKp), y:-> y@@ mKp >;
f:= DefiningPolynomial(L);
R<y> := PolynomialRing(Kp1);
 A:= [x @ mKp: x in Eltseq(f)];
  fp:=Polynomial(A);
//Roots(fp,Kp);
if IsIrreducible(fp) then
loc:= LocalField(Kp1, fp);
 else loc := LocalField(Kp1, Factorisation(fp)[1,1]);
 end if;
 Lp,mLp:= RamifiedRepresentation(loc);
// "map mLp is isomorphism from loc to Lp";
//  mLp:= hom<L_abs->Lp| x:-> Lp![(z@mKp)@mLp: z in Eltseq(L!x)] ,
  //                 y:->L_abs!(L![(z@@ mLp)@@ mKp: z in Eltseq(y)])    >;

//mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(Evaluate(Polynomial([ z@@ mKp : z in Eltseq(y@@ mLp)]),L.1))>;
mLp:=hom<L_abs->Lp |x:->mLp(loc![z@ mKp: z in Eltseq(L!x)])  , y:-> L_abs!(L!(L_elt([ z@@ mKp : z in Eltseq(y@@ mLp)],L)))>;

return Lp,mLp;

end intrinsic;

intrinsic L_elt(A,L)->.
{ Add 0 in arguments so that coercion can be calculated.}

 assert #A le Degree(L);
 // "if assertion fails it means Kp eq Lp in the relative completion";
if #A eq Degree(L) then
   return  A;
   else repeat Append(~A,0);
         until #A eq Degree(L);
     return A;
end if;
end intrinsic;




/*
intrinsic Relative_Completion1(L:: FldNum, K::FldNum, p:: RngIntElt)->.
{Completion of Relative field Lw/Kv such that w is a place over v}
return relative_completion1(L,K,p);
end intrinsic;

intrinsic Relative_Completion(L:: FldNum, K::FldNum, p:: RngIntElt)->.
{Completion of Relative field Lw/Kv such that w is a place over v}
 
 L_abs:=AbsoluteField(L);
P:=Decomposition(MaximalOrder(K),p)[1,1];

 e:= Completion(MaximalOrder(L_abs), Decomposition(MaximalOrder(L_abs),p)[1,1]) ;
 if RamificationDegree(e) in [Degree(L,K), AbsoluteDegree(L_abs)] then 
  return false, "Not Computable! Try self to find the problem";
end if;
 if RamificationDegree(e) eq 1 then
    if AbsoluteDegree(e) lt Degree(L,K)  then
       return false, "Not Computable! Try self to find the problem";
     else return relative_completion(L,K,p);
     end if;
     else return relative_completion(L,K,p);
     end if;
end intrinsic;

*/





intrinsic gfcUndecomposed_relative(L::FldNum, K:: FldNum, p0::RngIntElt : psiL := 0) -> ModCoho, Map, ModTupRngElt, Rec
{ Computes the global fundamental class for a number field L
  in which the prime p0 is undecomposed.
  Optionally one can pass the Galois action on L as map G->Aut(L/Q).
}

 L_abs:=AbsoluteField(L);
//assert RamificationDegree(Completion(MaximalOrder(L_abs), Decomposition(MaximalOrder(L_abs),p0)[1,1])) le Degree(L,K);
    require IsTotallyReal(L) :
            "Just implemented for totally real fields!";
    require #Decomposition(L,p0) eq 1 :
            "Prime must be undecomposed in L!";

//Lp,mLp:=Relative_Completion(L,K,p0);
//mLp:= map<L_abs->Lp| x:-> mLp(L!x) , y:-> L_abs!(y @@ mLp)>; 
t := Cputime();
    if psiL cmpeq 0 then
        G,_, psiL := AutomorphismGroup(L_abs);
        psiL := map< Domain(psiL) -> Codomain(psiL) | x:-> psiL(x^(-1)) >;
    else
        G := Domain(psiL);
    end if;
/*
    H:=AutomorphismGroup(L,K);
    H:=sub<G|H>;
    HH := [x: x in H];
  */
vprint GFC, 1: "compute primes";
    IndentPush();
    //primes := {p0} join {x[1] : x in Factorization(Discriminant(RingOfIntegers(K)))};
  primes := {p0} join {x[1] : x in Factorization(Discriminant(RingOfIntegers(L_abs)))}; 
  
   subL := Subfields(L_abs);
    for sub in subL do
        F := sub[1];
        CG, m := ClassGroup(F: Bound := BachBound(F));
        S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);

        CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        while #CGmod gt 1 do
            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
        primes := Setseq({Generator(s meet Integers()) : s in S});
    end for;
    //primes := Setseq({Generator(s meet Integers()) : s in S});
    S := &cat([  [Ideal(x[1]) : x in Decomposition(L_abs,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();

    OL_abs := RingOfIntegers(L_abs);

 vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 2: US, mUS := SUnitGroup(S);
    GG := [sig : sig in G];
    vtime GFC, 2: sigUS := SUnitAction(mUS, [psiL(sig) : sig in G],S);
    psiUS := map< G -> Aut(US) | sig :-> sigUS[Index(GG,sig)] >;
    IndentPop();

    H:=FixedGroup(L_abs,L);
   K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i) 
          :  i in [1..#Generators(US)]])), D))): h in H ] 
	  where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);
   
   US0 := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in K0]);
   mUS0 := map< US0 -> L | x :-> L!((US!x) @ mUS) >;

    
    
    
    
    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JL";
    IndentPush();
    lst := [];
    thetaAll := [];
    // construct JL
    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();

        PL := Factorization(p*OL_abs)[1,1];
        piL := UniformizingElement(PL);

 vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PL) eq 1 then
            theta := OL_abs!1;
            m := 0;
        else
            theta, m := lattice(PL, piL, psiL);
        end if;
        Append(~thetaAll, OL_abs!theta);
        vprint GFC, 2: "Time:", Cputime(t);

        vprint GFC, 2: "compute completion";
        LP, iotaL := Completion(L_abs, PL : Precision := 100);
  //phi:=hom<Lp->LP| x:->(x@@ mLp)@ iotaL, y:->(y @@ iotaL)@mLp>;       
	
	GP := [g : g in G | &and([  psiL(g)(x) in PL   : x in Generators(PL)]) ];
        GP := sub< G | GP>;
        psiLP := map< GP -> Aut(LP) | g :-> iotaL^(-1) * psiL(g) * iotaL >;
        vprint GFC, 2: "compute module";
        LIST:= [* LP,iotaL,psiLP*];
	
	ML, psiML, qML := compute_LPmul_modX_rel(L_abs, PL, psiL, LIST, theta, m);
        //ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, lat, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        indML, psiIndML, RL, kappaML, projML := inducedModule(ML, psiML, G);

     K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
         :  i in [1..#Generators(indML)]])), D))): h in H ]
	 where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);
	
    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);

     diagL := map< US0 -> indML0 | x :->
            &+([ x @ mUS0 @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;

        vprint GFC, 2: "compute cocycle";
        if p ne p0 then
            // trivial cocycle for this
            c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
        else
 // cocycle for p
            vtime GFC, 2: brGrp := LocalBrauerGroup(L_abs, p : autMap := psiL, lfc);

            c := TwoCocycle(brGrp`C, brGrp`lfc);
            C := Group(brGrp`C);
            // c := map< car<C,C> -> brGrp`M | x :-> c(x) @@ brGrp`f1 >;
            // c2 := map< Domain(c) -> Codomain(c) | x :-> c(x[2]^(-1), x[1]^(-1)) >;
            //testCocycle(c2, brGrp`actM );

            c2 := map< car<C,C> -> indML | x :-> c(x) @@ brGrp`f1 @@ brGrp`qM @ iotaL @ qML @ kappaML[1] >;
            // pre-compute images
            ll := [x : x in Domain(c2)];
            vtime GFC, 2: llImg := [c2(x) : x in ll];
            c2 := map< Domain(c2) -> Codomain(c2) | x :-> llImg[Index(ll, x)] >;

        end if;
        Append(~lst, [* indML0, psiIndML, diagL, c2 *]);
        IndentPop();
    end for;


    // infinite places
    vprint GFC, 1: "modules for infinite places";
    assert &and([ IsReal(inf) : inf in InfinitePlaces(L_abs) ]);
    H:=sub< FixedGroup(L_abs,K) | AutomorphismGroup(L)>;
HH := [x : x in H];
psiM := map< sub<H | Id(H)> -> Aut(US0) | sig :-> hom< US0 -> US0 | [US0.i : i in [1..#Generators(US0)]]> >;

//   H:=AutomorphismGroup(L,K);
  //  H:=sub<G|H>;
    indML, psiIndML, RL, kappaML, projML := inducedModule(US0, psiM, H);

   /* K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
      :  i in [1..#Generators(indML)]])), D))): h in H ]
       where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);
    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);
   */

   diagL := map< US0 -> indML | x :->
            &+([ x @ psiUS(RL[i]^(-1)) @ kappaML[i] : i in [1..#kappaML] ]) >;
    c2 := map< car<H, H> -> indML | x :-> Zero(indML) >;
    Append(~lst, [* indML, psiIndML, diagL,  c2 *] );
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    IndentPush();   
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);

// precompute projections
    vtime GFC, 2: projJL2 := [ hom< Domain(p) -> Codomain(p) | [ p(JL.i) : i in [1..#Generators(JL)]] >  : p in projJL ];
    // recomputation of projections using injections much faster

    vtime GFC, 2: actJL := [ hom< JL -> JL |
        [&+( [ JL.j @ projJL[k] @ lst[k,2](sig) @ inclJL[k] : k in [1..#lst]]) : j in [1..#Generators(JL)]]
        > :  sig in HH];
    psiJL := map< H -> Aut(JL) | sig :-> actJL[ Index(HH, sig) ] >;

 gamma := map< car<H, H> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;
    //gfcId := IdentifyTwoCocycle(CohJL, func< x | gamma(x[1],x[2]) @ f1JL >);
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // diagonal embedding of S-units
    embJL := map< US0 -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 2: B := [g @ embJL : g in Generators(US0)];
    CL, qCL := quo<JL | B>;
    // time homBasis := [ [CL.i @@ qCL @ psiJL(sig) @ qCL : i in [1..#Generators(CL)]] : sig in GG];
    // psiCL := map< G -> Aut(CL) | sig :->
    //     hom< CL -> CL | homBasis[Index(GG, sig)] >
    // >;
    psiCL := map< H -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< H -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 2: CohL := CohomologyModule(H, CL, psiCLr);
 // second cohom. group
    vtime GFC, 2: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) |
        x:-> Eltseq(x),
        y:-> CL!Eltseq(y)
    >;
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "Identify fundamental class:", Cputime(t);
    gammaC := map< car<G, G> -> CL | x :-> x @ gamma @ qCL >;
    gfcId := IdentifyTwoCocycle(CohL, func< x | gammaC(x[1],x[2]) @ f1CL >);

    inclUSJL := map< US0 -> JL | x :-> x @ diagL @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US := US, mUS := mUS,
        kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

    return  CohL, f1CL, gfcId, comp;
end intrinsic;

/*
intrinsic compute_LPmul_modX_rel(L, P, psiG,LIST, theta, m)->.
{}
return compute_LPmul_modX_relative(L, P, psiG,LIST, theta, m);
end intrinsic;

*/



intrinsic compute_LPmul_modX_rel(L, P,  psiG, LIST, theta, m)->.{}

  local G, GG, H, OL, piL,
          Q, pi_OL_Q, Qmal, i_Qmal_Q, phi_OL_Qmal, phi_Qmal_OL,
          expTheta, conjQ, S, pi_Qmal_S, actS, ZgenS,
          M, k, g, bilder, seq, proj, V;
LP:=LIST[1];
iota:=LIST[2];
psiL:=LIST[3];
  pi:=UniformizingElement(P);
//    LP, iota, psiL := completion_with_precision(L,P,psiG, m+10);
    G   := Domain(psiG);  GG := [g : g in G];
    H   := Domain(psiL);  HH := [g : g in H];
    OL  := MaximalOrder(L);
    piL := iota(pi);

    // X = exp(calL)
    // L_P^\times / X = ( L_P^\times / U^m ) / ( exp(L) / U^m )

    // ( L_P^\times / U^m ) = pi^\Z \times Q,
    // Q=(O_LP / P^m)^\times
    // Erzeuge Q und Qmal
    Q, pi_OL_Q := quo<OL | P^m>;
    Qmal, i_Qmal_Q := UnitGroup(Q);
    phi_OL_Qmal := pi_OL_Q*(i_Qmal_Q^(-1));
    phi_Qmal_OL := i_Qmal_Q*(pi_OL_Q^(-1));

 // Compute the exponential value of alpha truncated at the N's summand [Bley HS132, Remark 3.6].
    truncated_exp := func< alpha, N | &+( [  alpha^n/ Factorial(n) : n in [0..N] ] ) >;
    // Compute the precision to which the exponential function values must be known
    // to get correct results in L_P/exp(lattice).
    p := Generator(P meet Integers());
    N := Ceiling( m / (Valuation(theta, P) - RamificationIndex(P)/ (p-1)  ) );

    // exp(calL) in Q wird erzeugt von exp(theta)
    // brauche exp(theta) nur bis zu einer gewissen Genauigkeit
    expTheta := (iota^(-1))(truncated_exp(iota(theta),  N ));

    // expTheta und Konjugierte in Q lesen
    conjQ := [ phi_OL_Qmal( psiG(g)(expTheta) ) : g in HH];
    //H := sub<Qmal|conjQ>;
    S, pi_Qmal_S := quo<Qmal | sub<Qmal|conjQ> >;

    // Jetzt gilt: L_P^\times / X  =  pi^\Z \times S
    phi_OL_S := phi_OL_Qmal*pi_Qmal_S;
    phi_S_OL := phi_OL_S^(-1);

    // G-Wirkung auf S
    actS := map< car<G, S> -> S  |  x :-> phi_OL_S( psiG(x[1])( phi_S_OL(x[2]) ) ) >;
    // Z-Erzeuger
    ZgenS := [S.i : i in [1..#Generators(S)] ];

    // G-Wirkung auf L_P^\times / X  als Matrizen
    M := [];
    for k in [1..#HH] do
        g := HH[k];
        bilder := [];
        // Wirkung auf pi lokal
        bild := psiL(g)(piL);
        seq := ElementToSequence( phi_OL_S((iota^(-1))(bild/piL)));
        // Wirkung auf pi global
        //bild := psiG(g)(pi);
        //num,den:=numden(bild/pi, P);
        //seq := ElementToSequence(phi_OL_S(num)-phi_OL_S(den));
        Append(~bilder, [1] cat seq);

        bilder := bilder cat [ [0] cat ElementToSequence(actS(g,s) ) : s in ZgenS];
        Append(~M ,  Matrix(Integers(), bilder) );
    end for;
 Y:=FreeAbelianGroup(#ZgenS+1);
   mmY := map< H -> Aut(Y) | g :-> hom< Y -> Y |
        y :-> Y!Eltseq(Vector(Eltseq(y))*M[ Index(HH,g)]) > >;
    X, qX := quo<Y | [Order(ZgenS[i])* Y.(i+1) : i in [1..#ZgenS] ]>;
    mmX := map< H -> Aut(X) | g :-> hom< X -> X | x :-> qX( x@@qX @ mmY(g) ) > >;

    // Projektion (lokale Rechnung)
    f := map< LP -> X |
      //x :->  qX(Y!([Valuation(x)] cat Eltseq(phi_OL_S((iota^(-1))(x/piL^Valuation(x)))))) ,
      x :->  qX(Y!([Valuation(x)] cat Eltseq( (x/piL^Valuation(x)) @@ iota @ phi_OL_S ))) ,
      y :->  piL^yy[1]*iota(phi_S_OL(S!yy[2..#yy])) where yy := Eltseq( y @@ qX )
    >;

    return X, mmX, f;
end intrinsic;













/////////////////////////////////////////////////////////////////////////////////////////////////////////////AutomorphismGroup//////////////////////////////////////////////////////////////////////////////////////////////////////////////////




declare attributes Map:LocalAutoGenerators;
declare attributes Map:LocalRingMap;

function eval_automorphism(x, gens, pos)
    if pos eq #gens then
        return x;
    end if;

    R := Parent(x);
    P := PolynomialRing(R);
    return Evaluate(
        P ! [eval_automorphism(i, gens, pos + 1) : i in Eltseq(x)], gens[pos]
    );
end function;



intrinsic Continuations(m::Map, L::RngPad) -> SeqEnum
{Let m: R -> R be an automorphism of a p-adic ring.
Let L be an extension of R.  Return the continuations of m to L.}

    R := BaseRing(L);
    f := DefiningPolynomial(L);

    if R ne Domain(m) then
      return Flat([Continuations(mm, L): mm in Continuations(m,R)]);
    end if;

    S := Codomain(m);

    res := [];
    if Degree(L, R) eq 1 then
        curr := map<L -> S | x :-> S ! m(R ! x)>;
        curr`LocalAutoGenerators := ChangeUniverse(m`LocalAutoGenerators, S);
        Append(~res, curr);
    elif IsInertial(f) and Domain(m) eq PrimeRing(L) then
      //CF: in general, if m is the identity on the coefficient ring
      //    this method is (would be) legal.
        gens := ChangeUniverse(m`LocalAutoGenerators, S);
        r := L.1;
        for i in [1..Degree(L)] do
            curr_gens := Insert(gens, 1, r);
            curr := map<L -> S | x :-> S!eval_automorphism(x, curr_gens, 1)>;
            curr`LocalAutoGenerators := curr_gens;
//"curr_gens",curr_gens;
            Append(~res, curr);
            r := GaloisImage(r, 1);
        end for;
    else
        P := PolynomialRing(S);
        gens := ChangeUniverse(m`LocalAutoGenerators, S);
        roots := Roots(P ! [m(x) : x in Eltseq(f)]);
        i := 0;
        repeat
            i +:= 1;
        until i gt #roots or IsWeaklyEqual(roots[i][1], L.1);
        if i le #roots then
            ri := roots[i];
            Remove(~roots, i);
            Insert(~roots, 1, ri);
        end if;
        for r in roots do
            curr_gens := Insert(gens, 1, r[1]);
           curr := map<L -> S | x :-> eval_automorphism(x, curr_gens, 1)>;
            curr`LocalAutoGenerators := curr_gens;
//"curr_gens",curr_gens;    
            Append(~res, curr);
        end for;
    end if;
    return res;
"res",[IsWeaklyEqual(m(Domain(m).1), Domain(m).1) : m in res];

end intrinsic;


intrinsic Automorphisms(L::RngPad, K::RngPad: Into := false) -> SeqEnum
{Return the automorphisms of the local ring L over K. Automorphisms are returned as a sequence of maps}
  if Into cmpeq false then
    Into := L;
  end if;

    if L eq K then
        curr_gens := [Into ! 1];
        curr := map<L -> Into | x :-> eval_automorphism(x, curr_gens, 1)>;
//"curr_gens",curr_gens;              
        curr`LocalAutoGenerators := curr_gens;
        return [curr];
    end if;
//"L",L;
//"BaseRing(L)",BaseRing(L);
    R := BaseRing(L);
    require R ne L : "Argument 1 must be an extension of argument 2";
    maps := Automorphisms(R,K : Into := Into);

    res := [];
        for m in maps do
           res cat:= Continuations(m,L);
        end for;
    return res;
"maps",[IsWeaklyEqual(m(Domain(m).1), Domain(m).1) : m in maps];
"maps",[m(Domain(m).1)  : m in maps];
"res",[m(Domain(m).1)  : m in res];
end intrinsic;


intrinsic Automorphisms(L::RngPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
  return Automorphisms(L, PrimeRing(L));
end intrinsic;


function eval_field_automorphism(x, m)
    F := Parent(x);
    R := RingOfIntegers(F);
    pi := UniformizingElement(F);

    xv := Valuation(x);
    xu := ShiftValuation(x, -xv);
    return (F ! m(UniformizingElement(R)))^xv * F ! m(R ! xu);
end function;

function construct_field_map(L, m)
    res := map<L -> L | x :-> eval_field_automorphism(x, m)>;
    res`LocalRingMap := m;
    return res;
end function;




////////////////////////////////////////////////////////////////////////


intrinsic Automorphisms(L::FldPad,K::FldPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
    maps := Automorphisms(RingOfIntegers(L),RingOfIntegers(K));
    return [construct_field_map(L, m) : m in maps];
end intrinsic;

intrinsic Automorphisms(L::FldPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
    maps := Automorphisms(RingOfIntegers(L));
    return [construct_field_map(L, m) : m in maps];
end intrinsic;


function auto_eq(m1, m2)
    return m1`LocalAutoGenerators eq m2`LocalAutoGenerators;
end function;

function auto_mult(m1, m2)
    gens1 := m1`LocalAutoGenerators;
    gens2 := m2`LocalAutoGenerators;
    gens := [];
    for i in [1..#gens1] do
        Append(~gens, eval_automorphism(gens1[i], gens2, 1));
    end for;

    L := Universe(gens1);
    m := map<L -> L | x :-> eval_automorphism(x, gens, 1)>;
    m`LocalAutoGenerators := gens;
    return m;
end function;


intrinsic AutomorphismGroup(L::RngPad,K::RngPad: Abelian:= false) -> Grp, Map, PowMapAut
{Return the automorphism group of L/K as a permutation group}

    maps := Automorphisms(L,K); // maps[1] need not be identity
    assert auto_eq(auto_mult(maps[1],maps[1]),maps[1]);

    if not Abelian then
      G, m1 := GenericGroup
      (maps : Mult := auto_mult, Eq := auto_eq ,Id := maps[1] //WRONG! MW, Fixed NS
      );
      m2, G2 := CosetAction(G, sub<G|>);
      m := Inverse(m2) * m1;
      return
        G2,
        map<
            G2 -> PowerStructure(Map) | g :-> m(g), h :-> h @@ m
        >,Aut(L);
    else
       G, m1 := GenericGroup
        (maps : Mult := auto_mult, Eq := auto_eq, Id := maps[1] //WRONG! MW, Fixed NS
      );
      //if not IsAbelian(G) then
      //  error "AutomorphismGroup: ERROR, you claimed the group is abelian, this is not the case.";
      //end if;
      m2, G2 := CosetAction(G, sub<G|>);
      m := Inverse(m2) * m1;
      Gab, mab := AbelianGroup(G2);
      return
        Gab,
        map<
            Gab -> PowerStructure(Map) | g :-> m(g @@ mab), h :-> mab(h @@ m)
        >,Aut(L);
    end if;
end intrinsic;


intrinsic AutomorphismGroup(L::FldPad,K::FldPad: Abelian:= false) -> Grp, Map, PowMapAut
{Return the automorphism group of L over K as a permutation group}
    G, m := AutomorphismGroup(RingOfIntegers(L),RingOfIntegers(K):Abelian:=Abelian);

    return
        G,
        map<
            G -> PowerStructure(Map) |
            g :-> construct_field_map(L, m(g)),
            h :-> h`LocalRingMap @@ m
        >, Aut(L);
end intrinsic;

intrinsic AutomorphismGroup(L::FldPad) -> Grp, Map, PowMapAut
{Return the automorphism group of L as a permutation group}
  G,m := AutomorphismGroup(L,PrimeField(L));
  return G,m,Aut(L);
end intrinsic;




function prim_elt(L, K)
        //print "primitive_element";
    E := BaseRing(L);
    if E eq K then
        return L.1, MinimalPolynomial(L.1);
    else
        alpha := L.1;
        //print("Berechne primitives Element rekursiv");
        beta := prim_elt(E,K);
        //print beta;
        n := Degree(L,K);
        for j in [1..10] do
            gamma := Random(1,10)*alpha + beta;
            //print "berechne MiPo";
            f := MinimalPolynomial(gamma,K);
            if Type(K) eq RngPad then
                f := PolynomialRing(FieldOfFractions(K))!f;
            end if;
            try
                //print "faktorisiere quadratfrei";
                //f := SquareFreeFactorization(f)[1,1];
                //print "faktorisiere";
                if Degree(Factorization(f)[1,1]) eq n then
                    return gamma, f;
                end if;
            catch e
                gamma := 0;
            end try;
        end for;
        error "Did not find a primitive element!";
    end if;
end function;


intrinsic primitive_element(L:: FldPad,K:: FldPad)->.
{}
return prim_elt(L,K);
end intrinsic;

intrinsic primitive_element(L:: RngPad,K:: RngPad)->.
{}
return prim_elt(L,K);
end intrinsic;





////////"Computing Cohomology group and gfc for relative subfields of cyclic numberfield"///////////////////////////////////////////////////////////////////////////////////////// 






intrinsic gfcCompositum_relative(L::FldNum, L1::FldNum) -> ModCoho, Map, ModTupRngElt, Rec
{ Given an arbitrary "relative" Galois extension L/K and a cyclic extension L1/Q or Suitable
  of the same degree, this method computes then global fundamental
  class of L/K.
}

   // require IsCyclic(L1) and Degree(L) eq Degree(L1) :
     //       "Second number field must be cyclic and of the same degree!";
require IsCyclic(L1):"Second number field must be cyclic";
    t := Cputime();

    vprint GFC, 1: "compute composite field";
    IndentPush();
//    vtime GFC, 1: N := OptimizedRepresentation(Compositum(L,L1));
    N:=OptimisedRepresentation(Compositum(AbsoluteField(L),AbsoluteField(L1)));
    N1:=RelativeField(BaseField(L),N); 
  //  assert IsTotallyReal(N);
    ON := RingOfIntegers(N);

    Gamma, _ ,psiN := AutomorphismGroup(N);
    psiN := map< Domain(psiN) -> Codomain(psiN) | x :-> psiN(x^(-1)) >;
    IndentPop();
   L_abs:=AbsoluteField(L);
   L1_abs:=AbsoluteField(L1);
    OL_abs := RingOfIntegers(L_abs);

    vprint GFC, 1: "compute primes";
    IndentPush();
    // ramified primes
    primes := [f[1] : f in Factorization(Discriminant(ON))];
   

 prime:=trivialSclassless(L_abs,L1_abs,N);
    primes:=&cat[prime,primes];
    set:={x: x in primes};
    primes:=[x : x in set];
     seq := [p :   p in primes | #Decomposition(L1_abs, p) eq 1];
if #seq eq 0 then
    p0:=findUndecomposedPrime(L1_abs);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;

S := &cat([  [Ideal(x[1]) : x in Decomposition(N,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();

    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 1: US, mUS := SUnitGroup(S);
    GammaSeq := [sig : sig in Gamma];
    vtime GFC, 1: sigUS := SUnitAction(mUS, [psiN(sig) : sig in GammaSeq],S);
    psiUS := map< Gamma -> Aut(US) | sig :-> sigUS[Index(GammaSeq,sig)] >;


   HN1:=FixedGroup(N,N1); 
    KN1 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)
          :  i in [1..#Generators(US)]])), D))): h in HN1 ]
          where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);

   US0 := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in KN1]);
   mUS0 := map< US0 -> N1 | x :-> N1!((US!x) @ mUS) >;


    HL := AutomorphismGroup(N1,L);
    KL := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(US0.i @ psiUS(h) - US0.i)  :  i in [1..#Generators(US0)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(US0.i) :  i in [1..#Generators(US0)] ]);
    USL0 := &meet([sub<US0| [US!Eltseq(b)[1..#Generators(US0)] :  b in Basis(k)]> : k in KL]);

/*
 H:=FixedGroup(L_abs,L);
   K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)
          :  i in [1..#Generators(US)]])), D))): h in H ]
          where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);

   US0 := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in K0]);
   mUS0 := map< US0 -> L | x :-> L!((US!x) @ mUS) >;

*/



//"It works only with  mUS so check the map US0";
//
 assert &and([ g @ mUS in L : g in Generators(USL0)]);
    IndentPop();

    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JN";
    IndentPush();
    lst := [];
    thetaAll := [];



// vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);
    
    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();
        PN := Factorization(p*ON)[1,1];
        piN := UniformizingElement(PN);

        vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PN) eq 1 then
            theta := ON!1;
            m := 0;
        else
            theta, m := lattice(PN, piN, psiN);
            for i in [1..2] do
               theta1, m1 := lattice(PN, piN, psiN);
                if m1 lt m then
                    theta := theta1;
                    m := m1;
                end if;
            end for;
        end if;
        Append(~thetaAll, ON!theta);
        vprint GFC, 2: "Time:", Cputime(t);

  /*   if p eq 2 then
       // print "compute completion, prec =", Max(100,m*2);
        NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;
       */

        NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;

        //print "completion with sufficient precicion for computations up to precision ", m+10;
        vprint GFC, 2: "compute completion, prec =", m+10;
       // vtime GFC, 2: NP, iotaN, psiNP := completion_with_precision1(N,PN,psiN, m+10);
    //   end if;
       LIST:=[*NP,iotaN,psiNP*];
        GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX1(N, PN, psiN,LIST, theta, m);
        // induce module
        vprint GFC, 2: "compute induced module";
       // H := FixedGroup(N,L);
        //R := [Gamma!x : x in r] where r := leftCosetRepresentatives(H, H meet GammaP);
        indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(MN, psiMN, Gamma);// : RepSys := R);
       // diagN := map< N -> indMN | x :->
        //    &+([ x @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;




      HN:=FixedGroup(N,N1);
    //HN:=AutomorphismGroup(N1);  
 
     KN := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)
         :  i in [1..#Generators(indMN)]])), D))): h in HN ]
         where D := DiagonalMatrix([Order(indMN.i)  :  i in [1..#Generators(indMN)] ]);

    indMN0 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)]  :b in Basis(k)]> : k in KN]);
    
     diagN0 := map< N1 -> indMN0 | x :->
            &+([ x  @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;  
    
    





HL := AutomorphismGroup(N1,L);
// H := AutomorphismGroup(N,L);
        KL := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN0.i @ psiIndMN(h) - indMN0.i)  :  i in [1..#Generators(indMN0)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(indMN0.i) :  i in [1..#Generators(indMN0)] ]);
        indML0 := &meet([sub<indMN0 | [indMN!Eltseq(b)[1..#Generators(indMN0)] :  b in Basis(k)]> : k in KL]);

/*  // "Not needed further action beacuse of Automorphism in Ralatuve ext works";
 *   HL := FixedGroup(N,L); "May not need to work since FixedGroup of (N,L) works here";
     K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
         :  i in [1..#Generators(indML)]])), D))): h in H ]
         where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);

    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);

     diagL := map< US0 -> indML0 | x :->
            &+([ x @ mUS0 @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;


*/

        assert (N1 !L.1) @ diagN0 in indML0;
        /*
        H := FixedGroup(N,L1);
        K := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
            : h in H ]
            where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
        indML1 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
        assert (N!L1.1) @ diagN in indML1;
        */
        if p ne p0 then
            // trivial cocycle for this
	    // "Here may be the problem because Aut(N1 or N) ";
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
            // compute cocycle for p
      
      
      HL1 := AutomorphismGroup(N,L1_abs);
      
      C, qC := quo< Gamma | HL1>;
            //psiL1 := map< C -> Aut(L1) | g :-> Coercion(L1,N) * psiN(g @@ qC) * Coercion(N,L1) >;
            psiL1 := map< C -> Aut(L1_abs) | g :->
                hom< L1_abs -> L1_abs | L1_abs.1 @ Coercion(L1_abs,N) @ psiN(g @@ qC) @ Coercion(N,L1_abs) >
            >;

            // compute ML1
            KL1 := [ Kernel(Transpose(HorizontalJoin(
                Transpose(Matrix([  Eltseq(indMN0.i @ psiIndMN(h) - indMN0.i)  :  i in [1..#Generators(indMN0)]])), D)))
                : h in HL1 ]
                where D := DiagonalMatrix([Order(indMN0.i) :  i in [1..#Generators(indMN0)] ]);
            indML1 := &meet([sub<indMN0 | [indMN0!Eltseq(b)[1..#Generators(indMN0)] :  b in Basis(k)]> : k in KL1]);
            psiIndML1 := map< C -> Aut(indML1) |
                sig :-> Coercion(indML1, indMN0)*psiIndMN(sig @@ qC)*Coercion(indMN0,indML1) >;

            // compute completion of L1
            //PL1 := Factorization(p*RingOfIntegers(L1))[1,1];
            PL1:= Factorization(p*RingOfIntegers(L1_abs))[1,1];

            //print "completion with sufficient precicion for computations up to precision ", m+10;
            vprint GFC, 2: "compute completion, prec =", m+10;
	   // L1P, iotaL1, psiL1P := completion_with_precision(AbsoluteField(L1),PL1,psiL1, m+10);
          

            //L1P, iotaL1, psiL1P := completion_with_precision1(L1,PL1,psiL1, m+10);
            // "Check here";
	    L1P, iotaL1 := Completion(L1_abs, PL1 : Precision := Max(100,m*2)); //Max(100,m*2));
            psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
             c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
             //c := CLocalFundamentalClassSerre(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
            // inflation
            c2 := map< car<Gamma,Gamma> -> indMN0 | x :-> c(x[1]@qC, x[2]@qC) @@ iotaL1 @ Coercion(L1,N) @ diagN0>;
            vprint GFC, 2: "test cocycle";
            vtime GFC, 2: assert testCocycleGenerators(c2, psiIndMN );
            c2 := map< Domain(c2) -> Codomain(c2) | x:-> c2(x[2]^(-1), x[1]^(-1)) >;
 end if;

        diagN0 := mUS0*diagN0;
        Append(~lst, [* indML0, indMN0, psiIndMN, diagN0, c2 *]);
        IndentPop();
    end for;
// infinite places
    vprint GFC, 1: "modules for infinite places";

  /////uncheck here
  
 Gamma1 :=sub< FixedGroup(N,BaseField(L)) | AutomorphismGroup(N1)>;
 GammaSeq1 :=[x: x in Gamma1];
  assert &and([ IsReal(inf) : inf in InfinitePlaces(N) ]);
    psiM := map< sub<Gamma1 | Id(Gamma1)> -> Aut(US0) | sig :-> hom< US0 -> US0 | [US0.i : i in [1..#Generators(US0)]]> >;
    indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(US0, psiM, Gamma1);
    diagN := map< US0 -> indMN | x :->
            &+([ x @ psiUS(RN[i]^(-1)) @ kappaMN[i] : i in [1..#kappaMN] ]) >;
    c2 := map< car<Gamma1, Gamma1> -> indMN | x :-> Zero(indMN) >;
    // Fix-module by H
    HL := AutomorphismGroup(N1,L);
    K := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
    indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
    assert &and([ x @ diagN in indML : x in Generators(USL0)]);

    Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *] );
    IndentPop();

vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    // Finitely generated idele group
    vprint GFC, 1: "compute idele group of N";
    IndentPush();
    JN, inclJN, projJN := DirectSum([o[2] : o in lst]);
    // recompute projections
    vtime GFC, 1: projJN := [ hom< Domain(p) -> Codomain(p) | [ p(JN.i) : i in [1..#Generators(JN)]] >  : p in projJN ];
    //projJN := [ hom< JN -> lst[k,2] |
       // [ Index(seq,i) eq 0 select lst[k,2]!0 else lst[k,2].(Index(seq,i))  : i in [1..#Generators(JN)]]
      //  >
    //    where seq := [Index(Eltseq(inclJN[k](lst[k,2].i)),1) : i in [1..#Generators(lst[k,2])]]
  //      : k in [1..#lst]];

    vtime GFC, 1: actJN := [ hom< JN -> JN |
        [&+( [ JN.j @ projJN[k] @ lst[k,3](sig) @ inclJN[k] : k in [1..#lst]]) : j in [1..#Generators(JN)]]
        > :  sig in GammaSeq1];
    psiJN := map< Gamma1 -> Aut(JN) | sig :-> actJN[ Index(GammaSeq1, sig) ] >;

    gamma := map< car<Gamma1, Gamma1> -> JN | x :-> &+([ x @ lst[i,5] @ inclJN[i]  : i in [1..#lst] ]) >;
    //gammaL := map< Domain(gamma) -> Codomain(gamma) | x :-> gamma(x[2]^(-1), x[1]^(-1)) >;
    //time testCocycleGenerators(gammaL, psiJN);
    IndentPop();

 vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of N";
 IndentPush();
    // diagonal embedding of S-units
    embJN := map< US0 -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 1: B := [g @ embJN : g in Generators(US0)];
    CN, qCN := quo<JN | B>;
    psiCN := map< Gamma1 -> Aut(CN) | sig :-> Inverse(qCN)*psiJN(sig)*qCN >;
    //gammaL := map< Domain(gamma) -> CN | x :-> gamma(x[2]^(-1), x[1]^(-1)) @ qCN >;
    //time testCocycleGenerators(gammaL, psiCN);
    IndentPop();
//"till here works well in 260 seconds around for S3":

 vprint GFC, 1: "compute cohomology of N";
    IndentPush();
    // compute cohomology
    // make right actions
    //psiCNr := map< Gamma -> Aut(CN) | g :-> psiCN(g^(-1)) >;
    psiCNr := map< Gamma1 -> Aut(CN) | g :-> psiCN(g^(-1)) >;
    vtime GFC, 1: CohN := CohomologyModule(Gamma1, CN, psiCNr);
    f1CN := map< CN -> RSpace(Integers(),Dimension(CohN)) | x:-> Eltseq(x), y:-> CN!Eltseq(y) >;
    // second cohom. group
    //time H2N := CohomologyGroup(CohN,2);
    vtime GFC, 1: H1N := CohomologyGroup(CohN,1);

    gammaC := map< car<Gamma1, Gamma1> -> CN | x :-> x @ gamma @ qCN >;
    //gfcId := IdentifyTwoCocycle(CohN, func< x | gammaC(x[1],x[2]) @ f1CN >);
    IndentPop();
//"till here also works well in 360 seconds around for S3":

vprint GFC, 1: "Time for cohomology of N:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    // Cohomology of L
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);

    embLN := map< JL -> JN |
        x :-> &+([ x @ projJL[i] @ Coercion(lst[i,1], lst[i,2]) @ inclJN[i] : i in [1..#lst]]),
        y :-> &+([ y @ projJN[i] @ Coercion(lst[i,2], lst[i,1]) @ inclJL[i] : i in [1..#lst]])
    >;
    G, qG := quo< Gamma1 | AutomorphismGroup(N1,L) >;
    psiJL := map< G -> Aut(JL) | sig :-> embLN * (sig @@ qG @ psiJN) * Inverse(embLN) >;

     vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    vtime GFC, 1: B := [g @ embJN @@ embLN : g in Generators(USL0)];
    CL, qCL := quo<JL | B>;

 psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();
    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 1: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    vtime GFC, 1: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) | x:-> Eltseq(x), y:-> CL!Eltseq(y) >;
    IndentPop();


    vprint GFC, 1: "Time for all the computation for L:", Cputime(t);
    t := Cputime();

    mUSL0 := map< USL0 -> L | x :-> L!(x @ mUS0) >;
    inclUSJL := map< USL0 -> JL | x :-> (US0!x) @ diagN @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, //gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US:= USL0, mUS := mUSL0,
        //kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

     Req:=[* G,qG,Gamma,gammaC,CL,qCL,CN,qCN,embLN,CohL,CohN,primes,f1CN,thetaAll *];



vprint GFC, 1: "find global fundamental class of L";
    IndentPush();
   for k in [ i : i in [1..Degree(L)] | GCD(i,Degree(L)) eq 1 ] do
    // for k in [ i : i in [1..Degree(L)]] do
     vprintf GFC, 1: ".";
        c := TwoCocycle(CohL, k*H2L.1);
        c2 := map< car< G, G> -> CL | x :-> c(<x[1],x[2]>) @@ f1CL >;
        c3 := map< car< Gamma, Gamma> -> CN | x :-> c2(x[1]@qG,x[2]@qG) @@ qCL @ embLN @ qCN>;
        //c4 := func< x | c3(x) @ f1CN>;
        dif := map< Domain(c3) -> Codomain(c3) | g :-> gammaC(g)-c3(g) >;
        bool, prog := IsTwoCoboundary(CohN, func< x | dif(x[1],x[2]) @ f1CN >);
        if bool then
            vprint GFC, 1: " found.";
            IndentPop();
            comp`gfcId := k*H2L.1;
           return CohL, f1CL, k*H2L.1, comp,Req;
        end if;
    end for;
    vprint GFC, 1: " failed.";
    IndentPop();
    error "Global fundamental class could not be found!!";

//return CohL, f1CL, H2L.1, comp,Req;
end intrinsic;




///////////////////////////////////checking relativegfc/////////////////////////







intrinsic gfcUndecomposed_relative_check(L::FldNum, K:: FldNum, p0 :: RngIntElt : psiL := 0) -> ModCoho, Map, ModTupRngElt, Rec
{ Computes the global fundamental class for a relative number field L/K
  in which the prime p0 is undecomposed.
  Optionally one can pass the Galois action on L as map G->Aut(L/K).
}

 L_abs:=AbsoluteField(L);
//assert RamificationDegree(Completion(MaximalOrder(L_abs), Decomposition(MaximalOrder(L_abs),p0)[1,1])) le Degree(L,K);
    require IsTotallyReal(L) :
            "Just implemented for totally real fields!";
    require #Decomposition(L,p0) eq 1 :
            "Prime must be undecomposed in L!";

//Lp,mLp:=Relative_Completion(L,K,p0);
//mLp:= map<L_abs->Lp| x:-> mLp(L!x) , y:-> L_abs!(y @@ mLp)>; 
t := Cputime();
    if psiL cmpeq 0 then
        G,_, psiL := AutomorphismGroup(L_abs);
        psiL := map< Domain(psiL) -> Codomain(psiL) | x:-> psiL(x^(-1)) >;
    else
        G := Domain(psiL);
    end if;
/*
    H:=AutomorphismGroup(L,K);
    H:=sub<G|H>;
    HH := [x: x in H];
  */
vprint GFC, 1: "compute primes";
    IndentPush();
    primes := {p0} join {x[1] : x in Factorization(Discriminant(RingOfIntegers(L_abs)))};
/*  
  prime1 :={x[1] : x in Factorization(Discriminant(RingOfIntegers(L_abs)))};
   u_prime := [p: p in prime1 | #Decomposition(L_abs,p) eq 1];

if #u_prime eq 0 then
   p0 := findUndecomposedPrime(L_abs);
   else p0 := u_prime[1];
end if;

   primes := {p0} join prime1;
  */
  subL := Subfields(L_abs);
    for sub in subL do
        F := sub[1];
        CG, m := ClassGroup(F: Bound := BachBound(F));
        S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);

        CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        while #CGmod gt 1 do
            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
        primes := Setseq({Generator(s meet Integers()) : s in S});
    end for;
    //primes := Setseq({Generator(s meet Integers()) : s in S});
    S := &cat([  [Ideal(x[1]) : x in Decomposition(L_abs,p)]  : p in primes]);

 vprint GFC, 1: primes;
    IndentPop();

    OL_abs := RingOfIntegers(L_abs);

 vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 2: US, mUS := SUnitGroup(S);
    GG := [sig : sig in G];
    vtime GFC, 2: sigUS := SUnitAction(mUS, [psiL(sig) : sig in G],S);
    psiUS := map< G -> Aut(US) | sig :-> sigUS[Index(GG,sig)] >;
    IndentPop();

    H:=FixedGroup(L_abs,L);
   K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)
          :  i in [1..#Generators(US)]])), D))): h in H ]
          where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);

   US0 := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in K0]);
   mUS0 := map< US0 -> L | x :-> L!((US!x) @ mUS) >;





    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JL";
    IndentPush();
    lst := [];
    thetaAll := [];
    // construct JL
    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();
        LP,iotaL := relative_completion(L,K,p,30);
	fac := Factorization(p*OL_abs);
      if #fac eq 1 then
       PL :=fac[1,1];
      //end if;
     else  fac_P := [fac[i,1]: i in [1..#fac]|  Valuation(Generators(fac[i,1])[2] @ iotaL) eq 1];
       if #fac_P ge 1 then
          PL := fac_P[1];
       else PL := Factorisation(p*OL_abs)[1,1];
       end if;
       end if;
     if RamificationIndex(PL) eq 1 then
        theta := OL_abs!1;
        m := 0;
       else
        theta, m := lattice_check(PL, psiL);
     end if;

    Append(~thetaAll, OL_abs!theta);


/*      PL := Factorization(p*OL_abs)[1,1];
        piL := UniformizingElement(PL);

 vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PL) eq 1 then
            theta := OL_abs!1;
            m := 0;
        else
            theta, m := lattice(PL, piL, psiL);
        end if;
        Append(~thetaAll, OL_abs!theta);
        vprint GFC, 2: "Time:", Cputime(t);

        vprint GFC, 2: "compute completion";
*/     
     
/*
     Kp,mKp := Completion(K,Decomposition(K,p)[1,1]: Precision:=20);
     KP1:= ChangePrecision(Kp,20);
     AA:=[x @ mKp : x in Eltseq(DefiningPolynomial(L))];
     fp := Polynomial(AA);
     loc := LocalField(KP1, fp);
     Lp,mLp:= RamifiedRepresentation(loc);
     iotaL := hom<L_abs->Lp| x:-> Lp![(z@mKp)@mLp: z in Eltseq(x)] ,y:->L_abs!(L![(z@@ mLp)@@ 
mKp: z in Eltseq(y)] )>; 
 */

 // LP,iotaL := relative_completion(L,K,p,20);
 autLP := Automorphisms(LP, pAdicField(LP));
     _,psiLP:=localized_automorphism_group(psiL, PL, iotaL, autLP);
      GP := Domain(psiLP);
     //changing for completion and decomposition
     
   //  LP, iotaL := Completion(L_abs, PL : Precision := 100);
  //phi:=hom<Lp->LP| x:->(x@@ mLp)@ iotaL, y:->(y @@ iotaL)@mLp>;

/*
        GP := [g : g in G | &and([  psiL(g)(x) in PL   : x in Generators(PL)]) ];
        GP := sub< G | GP>;
        psiLP := map< GP -> Aut(LP) | g :-> iotaL^(-1) * psiL(g) * iotaL >;
        vprint GFC, 2: "compute module";
	*/
        LIST:= [* LP,iotaL,psiLP*];

        ML, psiML, qML := compute_LPmul_modX_rel(L_abs, PL, psiL, LIST, theta, m);
        //ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, lat, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        indML, psiIndML, RL, kappaML, projML := inducedModule(ML, psiML, G);

     K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
         :  i in [1..#Generators(indML)]])), D))): h in H ]
         where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);

    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);

     diagL := map< US0 -> indML0 | x :->
            &+([ x @ mUS0 @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;

        vprint GFC, 2: "compute cocycle";
        if p ne p0 then
            // trivial cocycle for this
            c2 := map< car<G, G> -> indML | x :-> Zero(indML) >;
        else
 // cocycle for p
            vtime GFC, 2: brGrp := LocalBrauerGroup(L_abs, p : autMap := psiL, lfc);

            c := TwoCocycle(brGrp`C, brGrp`lfc);
            C := Group(brGrp`C);

            //testCocycle(c2, brGrp`actM );

            c2 := map< car<C,C> -> indML | x :-> c(x) @@ brGrp`f1 @@ brGrp`qM @ iotaL @ qML @ kappaML[1] >;
            // pre-compute images
            ll := [x : x in Domain(c2)];
            vtime GFC, 2: llImg := [c2(x) : x in ll];
            c2 := map< Domain(c2) -> Codomain(c2) | x :-> llImg[Index(ll, x)] >;

        end if;
        Append(~lst, [* indML0, psiIndML, diagL, c2 *]);
        IndentPop();
    end for;


    // infinite places
    vprint GFC, 1: "modules for infinite places";
    assert &and([ IsReal(inf) : inf in InfinitePlaces(L_abs) ]);

H:=sub< FixedGroup(L_abs,K) | AutomorphismGroup(L)>;  
HH := [x : x in H];
psiM := map< sub<H | Id(H)> -> Aut(US0) | sig :-> hom< US0 -> US0 | [US0.i : i in [1..#Generators(US0)]]> >;
  //  H:=AutomorphismGroup(L,K);
    //H:=sub<G|H>;
    indML, psiIndML, RL, kappaML, projML := inducedModule(US0, psiM, H);
    /* K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
      :  i in [1..#Generators(indML)]])), D))): h in H ]
       where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);
    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);
   */
   diagL := map< US0 -> indML | x :->
            &+([ x @ psiUS(RL[i]^(-1)) @ kappaML[i] : i in [1..#kappaML] ]) >;
    c2 := map< car<H, H> -> indML | x :-> Zero(indML) >;
    Append(~lst, [* indML, psiIndML, diagL,  c2 *] );
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    IndentPush();
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);
// precompute projections
    vtime GFC, 2: projJL2 := [ hom< Domain(p) -> Codomain(p) | [ p(JL.i) : i in [1..#Generators(JL)]] >  : p in projJL ];
    // recomputation of projections using injections much faster

    vtime GFC, 2: actJL := [ hom< JL -> JL |
        [&+( [ JL.j @ projJL[k] @ lst[k,2](sig) @ inclJL[k] : k in [1..#lst]]) : j in [1..#Generators(JL)]]
        > :  sig in HH];
    psiJL := map< H -> Aut(JL) | sig :-> actJL[ Index(HH, sig) ] >;

 gamma := map< car<H, H> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;
    //gfcId := IdentifyTwoCocycle(CohJL, func< x | gamma(x[1],x[2]) @ f1JL >);
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // diagonal embedding of S-units
    embJL := map< US0 -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 2: B := [g @ embJL : g in Generators(US0)];
    CL, qCL := quo<JL | B>;
    // time homBasis := [ [CL.i @@ qCL @ psiJL(sig) @ qCL : i in [1..#Generators(CL)]] : sig in GG];
    // psiCL := map< G -> Aut(CL) | sig :->
    //     hom< CL -> CL | homBasis[Index(GG, sig)] >
    // >;
    psiCL := map< H -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< H -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 2: CohL := CohomologyModule(H, CL, psiCLr);
 // second cohom. group
    vtime GFC, 2: H2L := CohomologyGroup(CohL,2);
    f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) |
        x:-> Eltseq(x),
        y:-> CL!Eltseq(y)
    >;
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "Identify fundamental class:", Cputime(t);
    gammaC := map< car<G, G> -> CL | x :-> x @ gamma @ qCL >;
    gfcId := IdentifyTwoCocycle(CohL, func< x | gammaC(x[1],x[2]) @ f1CL >);

    inclUSJL := map< US0 -> JL | x :-> x @ diagL @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US := US, mUS := mUS,
        kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

    return  CohL, f1CL, gfcId, comp;
end intrinsic;













intrinsic gfcCompositum_relative_check(L::FldNum, L1::FldNum) -> ModCoho, Map, ModTupRngElt, Rec
{ Given an arbitrary "relative" Galois extension L/K and a cyclic extension L1/Q or Suitable
  of the same degree, this method computes then global fundamental
  class of L/K.
}

   // require IsCyclic(L1) and Degree(L) eq Degree(L1) :
     //       "Second number field must be cyclic and of the same degree!";
require IsCyclic(L1):"Second number field must be cyclic";
    t := Cputime();

    vprint GFC, 1: "compute composite field";
    IndentPush();
//    vtime GFC, 1: N := OptimizedRepresentation(Compositum(L,L1));
//    N:=OptimisedRepresentation(Compositum(AbsoluteField(L),AbsoluteField(L1)));
  N1 :=compositum_relative(L,L1);
  N:=AbsoluteField(N1);
//N1:=RelativeField(BaseField(L),N);
  //  assert IsTotallyReal(N);
    ON := RingOfIntegers(N);

    Gamma, _ ,psiN := AutomorphismGroup(N);
    Gamma1:=AutomorphismGroup(N1);
    psiN := map< Domain(psiN) -> Codomain(psiN) | x :-> psiN(x^(-1)) >;
    IndentPop();
   L_abs:=AbsoluteField(L);
   L1_abs:=AbsoluteField(L1);
    OL_abs := RingOfIntegers(L_abs);

    vprint GFC, 1: "compute primes";
    IndentPush();
    // ramified primes
    primes := [f[1] : f in Factorization(Discriminant(ON))];


 prime:=trivialSclassless(L_abs,L1_abs,N);
    primes:=&cat[prime,primes];
    set:={x: x in primes};
    primes:=[x : x in set];
     seq := [p :   p in primes | #Decomposition(L1_abs, p) eq 1];
if #seq eq 0 then
    p0:=findUndecomposedPrime(L1_abs);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;

S := &cat([  [Ideal(x[1]) : x in Decomposition(N,p)]  : p in primes]);

    vprint GFC, 1: primes;
    IndentPop();

    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 1: US, mUS := SUnitGroup(S);
    GammaSeq := [sig : sig in Gamma];
    vtime GFC, 1: sigUS := SUnitAction(mUS, [psiN(sig) : sig in GammaSeq],S);
    psiUS := map< Gamma -> Aut(US) | sig :-> sigUS[Index(GammaSeq,sig)] >;


   HN1:=FixedGroup(N,N1);
    KN1 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)
          :  i in [1..#Generators(US)]])), D))): h in HN1 ]
          where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);

   US0 := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in KN1]);
   mUS0 := map< US0 -> N1 | x :-> N1!((US!x) @ mUS) >;


    HL := AutomorphismGroup(N1,L);
    KL := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(US0.i @ psiUS(h) - US0.i)  :  i in [1..#Generators(US0)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(US0.i) :  i in [1..#Generators(US0)] ]);
    USL0 := &meet([sub<US0| [US!Eltseq(b)[1..#Generators(US0)] :  b in Basis(k)]> : k in KL]);

 assert &and([ g @ mUS in L : g in Generators(USL0)]);
    IndentPop();

    vprint GFC, 1: "Time for set S:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "construct JN";
    IndentPush();
    lst := [];
    thetaAll := [];



// vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);

    for p in primes do
        vprint GFC, 1: "prime:", p;
        IndentPush();
       
       /* PN := Factorization(p*ON)[1,1];
        piN := UniformizingElement(PN);

        vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PN) eq 1 then
            theta := ON!1;
            m := 0;
        else
            theta, m := lattice(PN, piN, psiN);	   
            for i in [1..2] do
               theta1, m1 := lattice(PN, piN, psiN);	       
                if m1 lt m then
                    theta := theta1;
                    m := m1;
                end if;
            end for;
        end if;
        Append(~thetaAll, ON!theta);
        */
//	vprint GFC, 2: "Time:", Cputime(t);

//NP, iotaN := relative_completion(N1,BaseField(N1),p,Max(100,m*2));
NP, iotaN := relative_completion_check(N,N1,BaseField(N1),p,100);
if RamificationIndex(NP) eq 1 then
            theta := ON!1;
            m := 0;
	    PN := Factorization(p*ON)[1,1];
    else
    
    fac := Factorization(p*ON);
     fac_P := [fac[i,1]: i in [1..#fac]|  Valuation(Generators(fac[i,1])[2] @ iotaN) eq 1];
  if #fac_P ge 1 then
     PN := fac_P[1];
   else PN := Factorisation(p*ON)[1,1];
   end if;
 theta, m := lattice_check(PN, psiN);
  end if;
  Append(~thetaAll, ON!theta);
vprint GFC, 2: "Time:", Cputime(t);

// NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
// "below if we take Gamma1 then gfc will be more-tuple";
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;

        //print "completion with sufficient precicion for computations up to precision ", m+10;
        vprint GFC, 2: "compute completion, prec =", m+10;
       // vtime GFC, 2: NP, iotaN, psiNP := completion_with_precision1(N,PN,psiN, m+10);
    //   end if;
       LIST:=[*NP,iotaN,psiNP*];
        GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX1(N, PN, psiN,LIST, theta, m);
        // induce module
        vprint GFC, 2: "compute induced module";
       // H := FixedGroup(N,L);
        //R := [Gamma!x : x in r] where r := leftCosetRepresentatives(H, H meet GammaP);
        indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(MN, psiMN, Gamma);// : RepSys := R);
        diagN := map< N1 -> indMN | x :->
            &+([ x @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;



/*
      HN:=FixedGroup(N,N1);
    //HN:=AutomorphismGroup(N1);

     KN := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)
         :  i in [1..#Generators(indMN)]])), D))): h in HN ]
         where D := DiagonalMatrix([Order(indMN.i)  :  i in [1..#Generators(indMN)] ]);

    indMN0 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)]  :b in Basis(k)]> : k in KN]);

     diagN0 := map< N1 -> indMN0 | x :->
            &+([ x  @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;


*/




H := AutomorphismGroup(N1,L);
// H := AutomorphismGroup(N,L);

K := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
        indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);

        assert (N1 !L.1) @ diagN in indML;
/*

        KL := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN0.i @ psiIndMN(h) - indMN0.i)  :  i in [1..#Generators(indMN0)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(indMN0.i) :  i in [1..#Generators(indMN0)] ]);
        indML0 := &meet([sub<indMN0 | [indMN!Eltseq(b)[1..#Generators(indMN0)] :  b in Basis(k)]> : k in KL]);
*/
/*  // "Not needed further action beacuse of Automorphism in Ralatuve ext works";
 *   HL := FixedGroup(N,L); "May not need to work since FixedGroup of (N,L) works here";
     K0 := [ Kernel(Transpose(HorizontalJoin(Transpose(Matrix([  Eltseq(indML.i @ psiIndML(h) - indML.i)
         :  i in [1..#Generators(indML)]])), D))): h in H ]
         where D := DiagonalMatrix([Order(indML.i)  :  i in [1..#Generators(indML)] ]);

    indML0 := &meet([sub<indML | [indML!Eltseq(b)[1..#Generators(indML)]  :b in Basis(k)]> : k in K0]);

     diagL := map< US0 -> indML0 | x :->
            &+([ x @ mUS0 @ psiL(RL[i]^(-1)) @ iotaL @ qML @ kappaML[i] : i in [1..#kappaML] ]) >;


*/

//  assert (N1 !L.1) @ diagN in indML;


  if p ne p0 then
            // trivial cocycle for this
            // "Here may be the problem because Aut(N1 or N) ";
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
            // compute cocycle for p


      HL1 := AutomorphismGroup(N1, L1_abs);

      C, qC := quo< Gamma | HL1>;
            //psiL1 := map< C -> Aut(L1) | g :-> Coercion(L1,N) * psiN(g @@ qC) * Coercion(N,L1) >;
            psiL1 := map< C -> Aut(L1_abs) | g :->
                hom< L1_abs -> L1_abs | L1_abs.1 @ Coercion(L1_abs,N) @ psiN(g @@ qC) @ Coercion(N,L1_abs) >
            >;

            // compute ML1
            KL1 := [ Kernel(Transpose(HorizontalJoin(
                Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
                : h in HL1 ]
                where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
            indML1 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in KL1]);
            psiIndML1 := map< C -> Aut(indML1) |
                sig :-> Coercion(indML1, indMN)*psiIndMN(sig @@ qC)*Coercion(indMN,indML1) >;

            // compute completion of L1
            //PL1 := Factorization(p*RingOfIntegers(L1))[1,1];
            PL1:= Factorization(p*RingOfIntegers(L1_abs))[1,1];

            //print "completion with sufficient precicion for computations up to precision ", m+10;
            vprint GFC, 2: "compute completion, prec =", m+10;
           // L1P, iotaL1, psiL1P := completion_with_precision(AbsoluteField(L1),PL1,psiL1, m+10);


           // L1P, iotaL1,psiL1P := completion_with_precision1(L1,PL1,psiL1, m+10);
            // "Check here";
            L1P, iotaL1 := Completion(L1_abs, PL1 : Precision := Max(100,m*2)); //Max(100,m*2));
           //L1P, iotaL1 := relative_completion(L1,BaseField(L1),p, Max(100,m*2));
	   psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;

            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
            // c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
       //" tried with LFC with baseField only but fails";
       if p gt 50 then
	  c := CLocalFundamentalClassSerre_check(L1P, BaseField(L1P), m+5 : psi := psiL1P);
	  else
	  c := CLocalFundamentalClassSerre(L1P, BaseField(L1P), m+5 : psi := psiL1P);
           end if; 
	    // inflation
            c2 := map< car<Gamma,Gamma> -> indMN | x :-> c(x[1]@qC, x[2]@qC) @@ iotaL1 @ Coercion(L1,N) @ diagN>;
            vprint GFC, 2: "test cocycle";
            vtime GFC, 2: assert testCocycleGenerators(c2, psiIndMN );
            c2 := map< Domain(c2) -> Codomain(c2) | x:-> c2(x[2]^(-1), x[1]^(-1)) >;
 end if;

        diagN := mUS0*diagN;
        Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *]);
        IndentPop();
    end for;
// infinite places
    vprint GFC, 1: "modules for infinite places";

  /////uncheck here

// Gamma1 :=sub< FixedGroup(N,BaseField(L)) | AutomorphismGroup(N1)>;
  Gamma1 := AutomorphismGroup(N1);
 GammaSeq1 :=[x: x in Gamma1];
  assert &and([ IsReal(inf) : inf in InfinitePlaces(N) ]);
    psiM := map< sub<Gamma1 | Id(Gamma1)> -> Aut(US0) | sig :-> hom< US0 -> US0 | [US0.i : i in [1..#Generators(US0)]]> >;
    indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(US0, psiM, Gamma1);
    diagN := map< US0 -> indMN | x :->
            &+([ x @ psiUS(RN[i]^(-1)) @ kappaMN[i] : i in [1..#kappaMN] ]) >;
    c2 := map< car<Gamma1, Gamma1> -> indMN | x :-> Zero(indMN) >;
    // Fix-module by H
    HL := AutomorphismGroup(N1,L);
    K := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in HL ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
    indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
    assert &and([ x @ diagN in indML : x in Generators(USL0)]);

    Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *] );
    IndentPop();

vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    // Finitely generated idele group
    vprint GFC, 1: "compute idele group of N";
    IndentPush();
    JN, inclJN, projJN := DirectSum([o[2] : o in lst]);
    // recompute projections
    vtime GFC, 1: projJN := [ hom< Domain(p) -> Codomain(p) | [ p(JN.i) : i in [1..#Generators(JN)]] >  : p in projJN ];
    //projJN := [ hom< JN -> lst[k,2] |
       // [ Index(seq,i) eq 0 select lst[k,2]!0 else lst[k,2].(Index(seq,i))  : i in [1..#Generators(JN)]]
      //  >
    //    where seq := [Index(Eltseq(inclJN[k](lst[k,2].i)),1) : i in [1..#Generators(lst[k,2])]]
  //      : k in [1..#lst]];

    vtime GFC, 1: actJN := [ hom< JN -> JN |
        [&+( [ JN.j @ projJN[k] @ lst[k,3](sig) @ inclJN[k] : k in [1..#lst]]) : j in [1..#Generators(JN)]]
        > :  sig in GammaSeq1];
    psiJN := map< Gamma1 -> Aut(JN) | sig :-> actJN[ Index(GammaSeq1, sig) ] >;

    gamma := map< car<Gamma1, Gamma1> -> JN | x :-> &+([ x @ lst[i,5] @ inclJN[i]  : i in [1..#lst] ]) >;
    //gammaL := map< Domain(gamma) -> Codomain(gamma) | x :-> gamma(x[2]^(-1), x[1]^(-1)) >;
    //time testCocycleGenerators(gammaL, psiJN);
    IndentPop();

 vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele class group of N";
 IndentPush();
    // diagonal embedding of S-units
    embJN := map< US0 -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 1: B := [g @ embJN : g in Generators(US0)];
    CN, qCN := quo<JN | B>;
    psiCN := map< Gamma1 -> Aut(CN) | sig :-> Inverse(qCN)*psiJN(sig)*qCN >;
    //gammaL := map< Domain(gamma) -> CN | x :-> gamma(x[2]^(-1), x[1]^(-1)) @ qCN >;
    //time testCocycleGenerators(gammaL, psiCN);
    IndentPop();

//"till here works well in 260 seconds around for S3":

 vprint GFC, 1: "compute cohomology of N";
    IndentPush();
    // compute cohomology
    // make right actions
    //psiCNr := map< Gamma -> Aut(CN) | g :-> psiCN(g^(-1)) >;
    psiCNr := map< Gamma1 -> Aut(CN) | g :-> psiCN(g^(-1)) >;
    vtime GFC, 1: CohN := CohomologyModule(Gamma1, CN, psiCNr);
    f1CN := map< CN -> RSpace(Integers(),Dimension(CohN)) | x:-> Eltseq(x), y:-> CN!Eltseq(y) >;
    // second cohom. group
    //time H2N := CohomologyGroup(CohN,2);
    vtime GFC, 1: H1N := CohomologyGroup(CohN,1);

    gammaC := map< car<Gamma1, Gamma1> -> CN | x :-> x @ gamma @ qCN >;
    //gfcId := IdentifyTwoCocycle(CohN, func< x | gammaC(x[1],x[2]) @ f1CN >);
    IndentPop();
//"till here also works well in 360 seconds around for S3":

vprint GFC, 1: "Time for cohomology of N:", Cputime(t);
    t := Cputime();

    vprint GFC, 1: "compute idele group of L";
    // Cohomology of L
    JL, inclJL, projJL := DirectSum([o[1] : o in lst]);

    embLN := map< JL -> JN |
        x :-> &+([ x @ projJL[i] @ Coercion(lst[i,1], lst[i,2]) @ inclJN[i] : i in [1..#lst]]),
        y :-> &+([ y @ projJN[i] @ Coercion(lst[i,2], lst[i,1]) @ inclJL[i] : i in [1..#lst]])
    >;
    G, qG := quo< Gamma1 | AutomorphismGroup(N1,L) >;
    psiJL := map< G -> Aut(JL) | sig :-> embLN * (sig @@ qG @ psiJN) * Inverse(embLN) >;

     vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    vtime GFC, 1: B := [g @ embJN @@ embLN : g in Generators(USL0)];
    CL, qCL := quo<JL | B>;

 psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();
    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 1: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    vtime GFC, 1: H2L := CohomologyGroup(CohL,2);
 f1CL := map< CL -> RSpace(Integers(),Dimension(CohL)) | x:-> Eltseq(x), y:-> CL!Eltseq(y) >;
    IndentPop();


    vprint GFC, 1: "Time for all the computation for L:", Cputime(t);
    t := Cputime();

    mUSL0 := map< USL0 -> L | x :-> L!(x @ mUS0) >;
    inclUSJL := map< USL0 -> JL | x :-> (US0!x) @ diagN @ inclJL[#inclJL] >;

    comp := rec<GFCcomp |
        CohL := CohL, f1CL := f1CL, //gfcId := gfcId,
        CL := CL, psiCL := psiCL, qCL := qCL,
        primes := primes, US:= USL0, mUS := mUSL0,
        //kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;

     Req:=[* G,qG,Gamma,gammaC,CL,qCL,CN,qCN,embLN,CohL,CohN,primes,f1CN,thetaAll *];



vprint GFC, 1: "find global fundamental class of L";
    IndentPush();
   for k in [ i : i in [1..Degree(L)] | GCD(i,Degree(L)) eq 1 ] do
    // for k in [ i : i in [1..Degree(L)]] do
     vprintf GFC, 1: ".";
        c := TwoCocycle(CohL, k*H2L.1);
        c2 := map< car< G, G> -> CL | x :-> c(<x[1],x[2]>) @@ f1CL >;
        c3 := map< car< Gamma, Gamma> -> CN | x :-> c2(x[1]@qG,x[2]@qG) @@ qCL @ embLN @ qCN>;
        //c4 := func< x | c3(x) @ f1CN>;
        dif := map< Domain(c3) -> Codomain(c3) | g :-> gammaC(g)-c3(g) >;
        bool, prog := IsTwoCoboundary(CohN, func< x | dif(x[1],x[2]) @ f1CN >);
        if bool then
            vprint GFC, 1: " found.";
            IndentPop();
            comp`gfcId := k*H2L.1;
           return CohL, f1CL, k*H2L.1, comp,Req;
        end if;
    end for;
    vprint GFC, 1: " failed.";
    IndentPop();
    error "Global fundamental class could not be found!!";

//return CohL, f1CL, H2L.1, comp,Req;
end intrinsic;



intrinsic compositum_relative(K:: FldNum, L:: FldNum)->FldNum
{Compositum of relative extensions}

assert IsSimple(K) or IsSimple(L);
if IsSimple(K) then
lf := Factorisation(Polynomial(L, DefiningPolynomial(K)));
 assert forall{x : x in lf | x[2] eq 1 and Degree(x[1]) eq Degree(lf[1][1])};
 C := NumberField(lf[1][1]:Check := false, DoLinearExtension);
 else lf := Factorisation(Polynomial(K, DefiningPolynomial(L)));
 assert forall{x : x in lf | x[2] eq 1 and Degree(x[1]) eq Degree(lf[1][1])};
C := NumberField(lf[1][1]:Check := false, DoLinearExtension);
end if;
A := AbsoluteField(C);
Embed(K, A, A!C.1);
return RelativeField(BaseField(L),A);
end intrinsic;


