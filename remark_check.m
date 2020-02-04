intrinsic remark_check_mat(K::FldNum )->.{Torsion free Z[Gv]-module, "b" of Z[Gv]^b and its generators  }

Z :=Integers();
ZK :=MaximalOrder(K);
//Factorisation(Discriminant(ZK));
G, _, mG := AutomorphismGroup(K);
Gv :=DecompositionGroup(InfinitePlaces(K)[1]);
s := mG(Gv.1);
//fac := Factorisation(Discriminant(ZK));
S := [x[1] : x in Factorisation(Discriminant(ZK)*ZK)];
 U, mU := SUnitGroup(S);
q, mq := quo<U|U.1>;
hh := SUnitAction(mU, [s], S);
h := hom<q -> q | [q.i @@ mq @ hh[1] @mq : i in [1..Ngens(q)]]>;

MM :=Matrix([Eltseq(h(q.i)) : i in [1..Ngens(q)]]);
M := GModule(DecompositionGroup(InfinitePlaces(K)[1]), [MM]);
u :=IndecomposableSummands(M);
i := hom<q -> q | [h(q.i) - q.i : i in [1..Ngens(q)]]>;
//[h(y) eq y where y := q!Eltseq(M!x.1) : x in u];
j := hom<q -> q | [q.i + h(q.i) : i in [1..Ngens(q)]]>;
B :=Matrix([Eltseq(q.i@j): i in [1.. Ngens(q)]]);
Ker :=Kernel(B);
kgen := [q!Eltseq(Basis(Ker)[j]): j in [1..Dimension(Ker)]];
k :=sub<q|kgen>;
Im :=Image(B);
Xim := [q!Eltseq(Basis(Im)[j]): j in [1..Dimension(Im)]];
Xgen := [x@@j: x in Xim];
//k:=Kernel(j);
ik := hom<k -> q | [h(k.i) - k.i : i in [1..Ngens(k)]]>;
//X,mX:=quo<q|k>;
x,mx :=sub<q|Xgen>;
assert #quo<q|k,x> eq 1;
assert #(k meet x) eq 1;
m :=Image(i);
Q,mQ :=quo<m|Image(ik)>;
phi := hom<x->Q|[x.j @i @ mQ: j in [1..Ngens(x)]]>;
assert IsSurjective(phi);
A :=Matrix([Eltseq(x.i@phi): i in [1.. Ngens(x)]]);
A :=Matrix(GF(2),A);
a1,a2,a3 :=SmithForm(A);
a2z :=Matrix(Z,a2);
assert Determinant(a2z) in {1,-1};
xgen := [x!Eltseq(a2z[j]): j in [1..Ngens(x)] ];
//[phi(xgen[j]): j in [1..#xgen]];
Lmd := [xgen[j]@i-(phi(xgen[j]))@@mQ : j in [1..Ngens(Q)]];
   for j in [Ngens(Q)+1..Ngens(x)] do
      Append(~Lmd, (xgen[j]@i)@@i);
    end for;
Y :=[xgen[j]-Lmd[j] : j in [1..#xgen]];
assert #quo<q|[k.i: i in [1..Ngens(k)]],Y> eq 1;
V:=[q!k.i: i in [1..Ngens(k)]];
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
   for y in Y do
     Append(~V,y);
   end for;
return q, Ngens(k), V;

end intrinsic;

intrinsic remark_sunit(S,US,mUS,s )->.{Torsion free module, b,  basis elements, sigma-action,  }
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
K:=Domain(s);
q, mq := quo<US|US.1>;
hh := SUnitAction(mUS, [s], S);
h := hom<q -> q | [q.i @@ mq @ hh[1] @mq : i in [1..Ngens(q)]]>;

MM:=Matrix([Eltseq(h(q.i)) : i in [1..Ngens(q)]]);
M := GModule(DecompositionGroup(InfinitePlaces(K)[1]), [MM]);
u :=IndecomposableSummands(M);
i := hom<q -> q | [h(q.i) - q.i : i in [1..Ngens(q)]]>;
//[h(y) eq y where y := q!Eltseq(M!x.1) : x in u];
j := hom<q -> q | [ h(q.i) + q.i : i in [1..Ngens(q)]]>;
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
/*
  xgen1 :=[Q.i@@phi: i in [1..Ngens(Q)]];
 t,mt:= quo<x|[Q.i@@phi: i in [1..Ngens(Q)]]>;
 for i in [1..Ngens(t)] do
  Append(~xgen1,t.i @@mt );
  end for;
*/
A :=Matrix([Eltseq(x.i@phi): i in [1.. Ngens(x)]]);
A :=Matrix(GF(2),A);
a1,a2,a3 :=SmithForm(A);
a2z :=Matrix(Integers(),a2);
assert Determinant(a2z) in {1,-1};
xgen := [x!Eltseq(a2z[j]): j in [1..Ngens(x)] ];
assert &and([phi(x) eq Q!0: x in xgen[Ngens(Q)+1..#xgen]]);
//[phi(xgen[j]): j in [1..#xgen]];
Lmd := [(xgen[j]@i-(phi(xgen[j]))@@mQ)@@ik : j in [1..Ngens(Q)]];
//Lmd := [xgen[j]@i-(phi(xgen[j]))@@mQ : j in [1..Ngens(Q)]];
  for j in [Ngens(Q)+1..Ngens(x)] do
    Append(~Lmd, xgen[j]@i@@ik);
  end for;
//Y :=[xgen[j]-Lmd[j] : j in [1..#xgen]];
//assert #quo<q|[k.i: i in [1..Ngens(k)]],Y> eq 1;
/*V:=[q!k.i: i in [1..Ngens(k)]];
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
   for y in Y do
     Append(~V,y);
   end for;
 */

 v_act := SUnitAction(mUS,s,S);
 Y_b :=[xgen[j]-Lmd[j] : j in [1..Ngens(k)]];
 Y_a := [xgen[j]-Lmd[j] : j in [Ngens(k)+1 .. #xgen]];
//vv:=Y[Ngens(k)+1..#Y];
inv := [x:x in Y_a| v_act(x@@mq) - x@@mq eq US!0];
 vv := [x: x in Y_a| x notin inv];
  for x in inv do
     Append(~vv,x);
  end for;
   for i in [1..Ngens(k)] do
    Append(~vv, q!k.i);
    Append(~vv, Y_b[i]);
    end for;
  assert #quo<q|vv> eq 1;
return q,mq,Ngens(k),vv,h;
//return Ngens(q), Ngens(Q), #Y , quo<q|[k.i: i in [1..Ngens(k)]],Y>;
end intrinsic;


intrinsic psi_check(S,US,mUS,Gen,s,b)->.{}
 act := SUnitAction(mUS, s,S);
v:=[Gen[1], Gen[2] @ act];
//v:=[Gen[1], US.1+Gen[2]];
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



intrinsic make_positve(u, mUS)->.{Change the signs of SUnit gruop elements so that i_v(u) is positive where v is ramified infinite place.}

   if Sign(Real(Evaluate(u@mUS, InfinitePlaces(Codomain(mUS))[1]))) eq -1 then
         return -u;
     else return u;
   end if;
end intrinsic;





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

intrinsic action_inf_place(a)->.
{Interchange the generators with i->i+1 and i+1->i}
    E := Eltseq(a);
    aa := [];
  //  if IsEven(#E) then 
      for i in [1..#E-1] do
          if IsOdd(i) then
	     Append(~aa, E[i+1]);
	     Append(~aa,E[i]);
	   end if;  
	end for;
 // end if;	
  if IsOdd(#E) then 
     Append(~aa,E[#E]);
  end if;
  assert #E eq #Eltseq(aa);
 return aa;
end intrinsic;
