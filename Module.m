

//import "brauer.m"  : lattice_generator_theta, lattice, find_included_P_power_absolute;
     import "brauer.m"  :   compute_LPmul_modX;
  //  import "RelativeExtension.m"  :   CLocalFundamentalClassSerre_check;

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

/*

intrinsic findUndecomposedPrime(L::FldNum : max := 100) -> RngIntElt
{ Search for an undecomposed prime p in L with p<max. }

    if not IsAbelian(L) then
        OL := RingOfIntegers(L);
        ff := Factorization(Discriminant(OL));
        for f in ff do
            if #Decomposition(L,f[1]) eq 1 then
                return f[1];
            end if;
        end for;
        error "there exist no undecomposed primes!";
    end if;
    p := 2;
    while p lt max do
        if #Decomposition(L,p) eq 1 then
            return p;
        else
            p := NextPrime(p);
        end if;
    end while;
    error "no undecomposed prime below", max;
end intrinsic;
*/


intrinsic inducedModule(M::GrpAb, phi::Map, G::Grp : RepSys := 0) -> GrpAb, Map, SeqEnum, SeqEnum, SeqEnum
{ Given a (left) H-module M as abelian group with H-action by phi: H -> Aut(M)
  and H a subgroup of G. Compute the induced module N as a direct sum
  and return N, the G-action on N, a left representation system R of G/H,
  and sequences of embeddings M -> N and projections N -> M according to R.
}

    H := Domain(phi);

    if (#H eq #G) then
        return M, phi, [Id(G)], [ map< M->M | m:->m > ],  [ map< M->M | m:->m > ];
    end if;

    //N, iota := finiteSum(M, #G/#H);
    N, iota, proj := DirectSum([M : i in [1..#G/#H]]);

    // Left coset representatives
    R := leftCosetRepresentatives(G, H : RepSys := RepSys);

    // for all g in G, tau in R
    // compute r in R, h in H  such that  r*h=g*tau
    GG := [g : g in G];
    cosetAct := [[ [[*Index(R,r),h*] : r in R, h in H | r*h eq g*tau][1]   : g in GG] : tau in R];

    //cosetAct := map< car<G, R> -> car<R, H> |
    //    x :-> [ <r,h> : r in R, h in H | r*h eq x[1]*x[2] ][1]
    //>;

    // images from M into N w.r.t. tau in R
    B1 := [iota[i](m) : m in Generators(M), i in [1..#iota]];
    B2 := [[*m,i*] : m in Generators(M), i in [1..#iota]];

    // images of g*b using coset action
    images := [ [
        iota[c[1]]( phi(c[2])(B2[k,1]) )
        where c := cosetAct[B2[k,2], Index(GG,g)]
        where k := Index(B1,N.i) : i in [1..#Generators(N)]
    ] : g in GG];

    // G-action on M3
    psi := map< G -> Aut(N) | g :-> map< N -> N |
        x :-> &+([ y[i]*img[i]  : i in [1..#y]])  where img := images[Index(GG,g)] where y := Eltseq(x)
    > >;
    // print "check action";
    // // garantee correct G-action
    // assert &and({ psi(g)(psi(h)(b)) eq psi(g*h)(b) :   b in Generators(N), g in G, h in G});
    // // and correct embedding
    // assert &and({ iota[1](phi(h)(m)) eq  psi(h)(iota[1](m))   : m in Generators(M), h in H});

    return N, psi, R, iota, proj;
end intrinsic;





intrinsic lattice(P, pi, psi)->.{}
    local OL;
    OL := Order(P);
    if Degree(OL) eq AbsoluteDegree(OL) then
        return lattice_absolute(P,pi,psi);
    else
        return lattice_relative(P,pi,psi);
    end if;
end intrinsic;


intrinsic lattice_check(P, psi)->.{}
    local OL;
    OL := Order(P);
    pi := UniformizingElement(P);
    if Degree(OL) eq AbsoluteDegree(OL) then
        return lattice_absolute(P,pi,psi);
    else
        return lattice_relative(P,pi,psi);
    end if;
end intrinsic;


intrinsic lattice_absolute(P, pi, psiL)->.{}
    local OL, p, theta, v, v1, erz, x, M, ZpGtheta, k, m, M1, M1I, j, M2, T;
    
    OL := Order(P);
    p := Generator(P meet Integers());
    G := Domain(psiL);
    rand := false;
//Ali changed here!!!    
    
    repeat
        theta, v := lattice_generator_theta(psiL, P, pi, rand);
        rand := true;
        // erzeuger des Gitters global
        erz := [OL!(psiL)(g)(theta) : g in G];
        M := VerticalJoin( [Vector(ElementToSequence(x)) : x in erz ]);
        ZpGtheta := Lattice(M);
    until Rank(ZpGtheta) eq Degree(OL);
    
    // finde m mit P^m in ZpGtheta
    // einfacher Ansatz:
    k := Index(StandardLattice(Degree(OL)), ZpGtheta);
    m := Valuation(k*OL, P);
    //m := Valuation(k, setting`p)*RamificationIndex(setting`P);
    
    if m eq 0 or p eq 2 then
        return theta, v+1;
  
  end if;
    
    // kleinstes m
    // schreibe Basis von ZpGtheta in Matrix
    M1 := Matrix(Rationals(), [ElementToSequence(x) : x in erz]);
    M1I := M1^(-1);
    for j in [v+1..m] do
        m := j;
        // schreibe Basis von P^m in Matrix
        M2 := Matrix(Rationals(), [ElementToSequence(x) : x in Basis(P^j)]);
        // Basiswechsel durch T: M1*T=M2
        T := M1I*M2;
        // Elemente in T sollen nach Lokalisierung bei p ganz sein
        if not IsDivisibleBy(Denominator(T),p) then
            break;
        end if;
    end for;
    
    return theta, m;
end intrinsic;

intrinsic lattice_relative(P, pi, psiL)->.{}
    local OL,OK,p,G,theta,b,erz,g,M,x,y,ZpGtheta,k,m,M1,M1I,M2,j,T;
    
    OL := Order(P);
    OK := BaseRing(OL);
    assert(BaseRing(OK) cmpeq Integers());
    p := Generator(P meet Integers());
    G := Domain(psiL);
    rand := false;
    
    repeat
        theta, v := lattice_generator_theta(psiL, P, pi, rand);
        print theta;
        rand := true;
        // erzeuger des Gitters global
        erz := [OL!(psiL)(g)(theta) : g in G];
        // multiplizieren mit Basis von OK
        erz := [x*(OL!y) : x in erz, y in Basis(OK)];
        M := VerticalJoin( [Vector(&cat([ Eltseq(y) : y in Eltseq(x)])) : x in erz ]);
        ZpGtheta := Lattice(M);
    until Rank(ZpGtheta) eq AbsoluteDegree(OL) and &and([x in Integers() : x in Eltseq(M) ]);
    
    // finde m mit P^m in ZpGtheta
    // einfacher Ansatz:
    print M;
    k := Index(StandardLattice(AbsoluteDegree(OL)), ZpGtheta);
    m := Valuation(k*OL, P);
    
    if m eq 0 then
        return theta, v+1;
    end if;
    
    // kleinstes m
    // schreibe Basis von ZpGtheta in Matrix
    M1 := Matrix(Rationals(), M);
    M1I := M1^(-1);
    for j in [v+1..m] do
        m := j;
        // schreibe Basis von P^m in Matrix
        M2 := Matrix(Rationals(),  &cat([
            [ &cat([Eltseq(y) : y in Eltseq(b*x)]) : x in Basis(OK)]
            : b in Basis(P^j)
        ]));
        // Basiswechsel durch T: M1*T=M2
        T := M1I*M2;
        // Elemente in T sollen nach Lokalisierung bei p ganz sein
        if not IsDivisibleBy(Denominator(T),p) then
            break;
        end if;
    end for;
    
    return theta, m;
end intrinsic;

intrinsic lattice_generator_theta(psi, P, pi, rand)->.{}
    local OL, p, theta, v, v1;
    
    OL := Order(P);
    p := Generators(P meet Integers())[1];
   //checking here but doesn't work  
  theta := NormalBasisElement(OL, psi : rand := rand);
   // theta := NormalBasisElement_check(OL, psi : rand := rand);
    v := Valuation(theta, P);
    v1 := 1+Floor(AbsoluteRamificationIndex(P)/(p-1));
    v := Maximum(0,v1-v);
    theta := OL!(theta*(pi)^v);
    
    return theta, v;
end intrinsic;



function completion_with_precision1(L, P, psi, precision)
    local prec, min, err, compatible;

    if Generator(P meet Integers()) eq 2 then
        prec := Maximum(precision,50);
    else
        prec := Maximum(precision,50);
 	//prec := Maximum(precision,30);
    end if;

    repeat
        err := false;
        //Ali changed
//	compatible := false;
        try
            //print "compute completion", prec;
            LP, iota := Completion(L, P : Precision:=prec);
           // ChangePrecision(~LP,prec);
	   // iota:=map<L->LP| x:-> LP!iota(x)>;
	    autLP := Automorphisms(LP, pAdicField(LP));
            _, psiLP := localized_automorphism_group(psi, P, iota, autLP);
            /*H := [g : g in Domain(psi) | &and([  psi(g)(x) in P   : x in Generators(P)]) ];
            H := sub< Domain(psi) | H>;
            HH := [h : h in H];
            maps := [map< LP -> LP | x:-> x @@ iota @ psi(h) @ iota> :  h in HH];
            psiLP := map< H -> maps | h :-> maps[Index(HH,h)] >;
            */
            //print "test compatibility";
//"Ali changed to check for higher degree";
  
  /*min := Minimum(test_G_compatible(iota, psi, psiLP, true, 0)
                join test_G_compatible((iota)^(-1), psiLP, psi, false, P));
            compatible := (min ge precision);
*/
        catch e
            //print e`Object;
            err := true;
        end try;

        prec := 2*prec;
        if err then
            continue;
        end if;
  //  until (not err) and compatible;
until (not err);
    return LP, iota, psiLP;
end function;

function completion_with_precision(L, P, psi, precision)
    local prec, min, err, compatible;

    if Generator(P meet Integers()) eq 2 then
        prec := Maximum(precision,50);
    else
        prec := Maximum(precision,50);
        //prec := Maximum(precision,30);
    end if;

    repeat
        err := false;
        //Ali changed
      compatible := false;
        try
            //print "compute completion", prec;
            LP, iota := Completion(L, P : Precision:=prec);
           // ChangePrecision(~LP,prec);
           // iota:=map<L->LP| x:-> LP!iota(x)>;
            autLP := Automorphisms(LP, pAdicField(LP));
            _, psiLP := localized_automorphism_group(psi, P, iota, autLP);
            /*H := [g : g in Domain(psi) | &and([  psi(g)(x) in P   : x in Generators(P)]) ];
            H := sub< Domain(psi) | H>;
            HH := [h : h in H];
            maps := [map< LP -> LP | x:-> x @@ iota @ psi(h) @ iota> :  h in HH];
            psiLP := map< H -> maps | h :-> maps[Index(HH,h)] >;
            */
            //print "test compatibility";
//"Ali changed to check for higher degree";

  min := Minimum(test_G_compatible(iota, psi, psiLP, true, 0)
                join test_G_compatible((iota)^(-1), psiLP, psi, false, P));
            compatible := (min ge precision);

        catch e
            //print e`Object;
            err := true;
        end try;

        prec := 2*prec;
        if err then
            continue;
        end if;
    until (not err) and compatible;
//until (not err);
    return LP, iota, psiLP;
end function;

intrinsic completion_with_precision1(L, P, psi, precision)->.
{}
return completion_with_precision1(L, P, psi, precision);
end intrinsic;





intrinsic completion_with_precision(L, P, psi, precision)->.
{}
return completion_with_precision(L, P, psi, precision);
end intrinsic;


intrinsic localized_automorphism_group(m, P, iota, AutLoc)->.{}
    local G, GP, f, L, OL, Rts, RtsLok, i,j,prec,index, z, y, S;
    
    G := Domain(m);
    // Untergruppe von G
    //H := DecompositionGroup(P);
    GP := [g : g in G | &and([  m(g)(x) in P   : x in Generators(P)]) ];
    GP := sub< G | GP>;
    
    // Wenn G und H gleich sind, kann es sein, dass Magma die Gruppen
    // unterschiedlich aufzaehlt. D.h.
    // G eq H liefert true und 
    // [g : g in G] eq [g : g in H] liefert false
    
    // dieses Verhalten ist nicht ganz nachvollziehbar und wird
    // hiermit umgangen
    if G eq GP then
        GP := G;
    end if;
    
    L := Domain(m(GP.1));
    OL := Domain(AutLoc[1]);
    Rts := Roots(DefiningPolynomial(L), L);
    //RtsLok := Roots(ChangePrecision(Polynomial(OL, ElementToSequence(f)),OL`DefaultPrecision));
    RtsLok := Roots(DefiningPolynomial(L), OL);
    
    assert #Rts eq #RtsLok;
    
    // Zuordnung:    globale Nst x <-> lokale Nst y
    z := [];
    for i in [1..#Rts] do
        S := [ Valuation(RtsLok[j,1] - OL!iota(Rts[i,1])) : j in [1..#RtsLok] ];
        prec, index := Maximum(S);
        z := z cat [index];
    end for;
    //print z;
    
    // Zuordnung:    g in AutLoc <-> index von g(RtsLok[1]) in RtsLok
    y := [];
    for i in [1..#AutLoc] do
        S := [ Valuation(AutLoc[i](RtsLok[1,1]) - RtsLok[j,1] ) : j in [1..#RtsLok] ];
        //print S;
        prec, index := Maximum(S);
        y := y cat [index];
    end for;
    //print y;
    
    // Zuordnung:    Index globale Nst x  <->  Index von g in AutLoc, so dass g(RtsLok[1])=y
    z := [ Index(y, z[i]) : i in [1..#z] ];
    
    return GP, map< GP -> AutLoc | x :-> local_map(x, m, AutLoc, Rts, z) >;
end intrinsic;

intrinsic test_G_compatible(phi, actDom, actCodom, modP, prime)->.{}
    local D, B, gens, actD, actB, seq, U;
    
    if Type(prime) eq RngOrdIdl then
        modP := true;
    end if;
    
    D := Domain(phi);
    B := Codomain(phi);
    
    if Type(Domain(actDom)) ne SetCart then
        G := Domain(actDom);
        actD := map< car<G, D> -> D | x :-> actDom(x[1])(x[2]) >;
    else
        G := Component(Domain(actDom),1);
        actD := actDom;
    end if;
    
    if Type(Domain(actCodom)) ne SetCart then
        H := Domain(actCodom);
        //assert G eq Domain(actCodom);
        actB := map< car<H, B> -> B | x :-> actCodom(x[1])(x[2]) >;
    else
        H := Component(Domain(actCodom),1);
        //assert G eq Component(Domain(actCodom),1);
        actB := actCodom;
    end if;
    
    if G eq H then
        // groups equal
        U := G;
    else
        // take the smaller group
        if #H lt #G then
            U := H;
        else
            U := G;
        end if;
        // and make sure the elements can be read in the other group
       // assert &and([x in G and x in H :x in U]);
    end if;
    
    
    if Type(D) in {RngOrd, FldNum, ModTupRng, ModTupFld} then
        gens := Basis(D);
    elif Type(D) in {FldPad, RngPad} then
        gens := AbsoluteBasis(D);
    else
        print "not yet implemented: Generators/Basis for ", Type(D);
        try
            gens := Basis(D);
        catch e
            gens := Generators(D);
        end try;
    end if;
   //Ali changed for faster 
    if modP then
    seq:=[];
    for x in gens do
       for sig in U do
            Append(~seq,phi(actD(sig, x)) - actB(sig, phi(x)));
       end for; 
    end for; 
   //  seq := [ phi(actD(sig, x)) - actB(sig, phi(x)) : x in gens, sig in U];
        if Type(B) in {FldPad,RngPad} then
            return {Valuation(x) : x in seq};
        elif Type(B) in {FldNum,RngOrd} then
            if Type(prime) ne RngOrdIdl then
                error "Prime Ideal for Valuation needed!";
            end if;
            return {Valuation(x, prime) : x in seq};
        else
            error "not yet implemented: Valuation";
        end if;
    else
        //seq := [ [* sig, x, B!(phi(actD(sig, x)) - actB(sig, phi(x))) *] : x in gens, sig in G ];
        //print seq;
        return &and({ phi(actD(sig, x)) eq actB(sig, phi(x)) : x in gens, sig in U});
    end if;
end intrinsic;


intrinsic local_map(g, m, HomL, Rts, z)->.{}
//localMap(g::., m::Map, HomL::SeqEnum, Rts::SeqEnum, z::SeqEnum) -> Map
    // Nehme die globale Nst x0, die auf die erste lokale Nst abbildet
    first := Index(z,1);
    x := m(g)(Rts[first,1]);
    // Finde Index der globalen Nst x, so dass g(x0)=x
    S := [ x- Rts[i,1] : i in [1..#Rts] ];
    j := Index(S, 0);
    // Der Index der lokalen Abb, die das gleiche tut, steht in z
    return HomL[z[j]];
end intrinsic;



function compute_LPmul_modX1(L, P, psiG, LIST, theta, m)

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
    
    // L_P^\times / X  als abelian group 
/*if #ZgenS eq 0 then
 // Y:=AbelianGroup([NextPrime(Degree(L))]);
 Y:=AbelianGroup([5]);
 else
   Y:=FreeAbelianGroup(#ZgenS+1);
   end if;*/
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
end function;


//////////////////////////////No need of this basis/////////////////
intrinsic basis_pad(L, K)->.{}
    if (BaseRing(L) eq K) then
        n := Degree(L, K);
        return [L.1^(i-1) : i in [1..n]];
    else
        n := Degree(L); // ueber BaseRing
        B := basis_pad(BaseRing(L), K);
        return &cat([ [ L.1^(i-1)*b : b in B] : i in [1..n]   ]);
    end if;
end intrinsic;



intrinsic compute_LPmul_modX1(L, P, psiG,LIST, theta, m)->.
{}
return compute_LPmul_modX1(L, P, psiG,LIST, theta, m);
end intrinsic;


intrinsic gfcCompositumali(L::FldNum, L1::FldNum) -> ModCoho, Map, ModTupRngElt, Rec
{ Given an arbitrary Galois extension L/Q and a cyclic extension L1/Q
  of the same degree, this method computes then global fundamental
  class of L/Q.
}
    
    //require IsCyclic(L1) and Degree(L) eq Degree(L1) :
      //      "Second number field must be cyclic and of the same degree!";
    require IsCyclic(L1): "Second number field must be cyclic";
    t := Cputime();
    
    vprint GFC, 1: "compute composite field";
    IndentPush();
    vtime GFC, 1: N := OptimizedRepresentation(Compositum(L,L1));
    assert IsTotallyReal(N);
    ON := RingOfIntegers(N);
    
    Gamma, _ ,psiN := AutomorphismGroup(N);
    psiN := map< Domain(psiN) -> Codomain(psiN) | x :-> psiN(x^(-1)) >;
    IndentPop();
    
    OL := RingOfIntegers(L);
    
    vprint GFC, 1: "compute primes";
    IndentPush();
   
   // ramified primes
    primes := [f[1] : f in Factorization(Discriminant(ON))];
    // an undecomposed prime in L1
    seq := [p :   p in primes | #Decomposition(L1, p) eq 1];
//  if #seq eq 0 or seq[1] gt 50 then
  if  #seq gt 0 then
         p0 := Sort(seq)[1];
         else
       p0 := findUndecomposedPrime(L1);
        primes := Sort([p0] cat primes);
    end if;
    // trivial S-class numbers
   
   
// primes := [f[1] : f in Factorization(Discriminant(ON))];
//primes:=[p0];

// uncheck for other than transitive group
//vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);


//p0:=[p: p in primes| #Decomposition(L1,p) eq 1][1];
/*    seq := [i: i in primes| #Decomposition(L1,i) eq 1];
    if #seq eq 0 then
    p0:=findUndecomposedPrime(L1);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;*/
 vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);
    S := &cat([  [Ideal(x[1]) : x in Decomposition(N,p)]  : p in primes]);
    vprint GFC, 1: primes;
    IndentPop();
    
    vprint GFC, 1: "compute S-units and its G-action";
    IndentPush();
    // compute S-Units and G-action
    vtime GFC, 1: US, mUS,Base := SUnitGroup(S:Raw);
    GammaSeq := [sig : sig in Gamma];
    vtime GFC, 1: sigUS := SUnitAction(mUS, [psiN(sig) : sig in GammaSeq],S:Base :=Base);
    psiUS := map< Gamma -> Aut(US) | sig :-> sigUS[Index(GammaSeq,sig)] >;
    // S-units for L
    H := FixedGroup(N,L);
    K := [ Kernel(Transpose(HorizontalJoin(
        Transpose(Matrix([  Eltseq(US.i @ psiUS(h) - US.i)  :  i in [1..#Generators(US)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);
    USL := &meet([sub<US| [US!Eltseq(b)[1..#Generators(US)] :  b in Basis(k)]> : k in K]);
    //assert &and([ g @ mUS in L : g in Generators(USL)]);
//"time consuming"    assert &and([ PowerProduct(Base, mUS(g)) in L : g in Generators(USL)]);
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
          /*  for i in [1..2] do
                theta1, m1 := lattice(PN, piN, psiN);
                if m1 lt m then
                    theta := theta1;
                    m := m1;
                end if;
            end for;*/
        end if;
        Append(~thetaAll, ON!theta);
        vprint GFC, 2: "Time:", Cputime(t);
        
    /* if p eq 2 then    
	
        //print "compute completion, prec =", Max(100,m*2);
        NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        ChangePrecision(~NP,100);
	GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
       // psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;
       _, psiNP := localized_automorphism_group(psiN, PN, iotaN, Automorphisms(NP,PrimeField(NP)));
      else end if;*/  
        //print "completion with sufficient precicion for computations up to precision ", m+10;
        
	vprint GFC, 2: "compute completion, prec =", m+10;
        
	vtime GFC, 2: NP, iotaN, psiNP := completion_with_precision(N,PN,psiN, m+10);
        LIST:=[*NP,iotaN,psiNP*];
	GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX(N, PN, psiN,LIST, theta, m);
        // induce module
        vprint GFC, 2: "compute induced module";
        H := FixedGroup(N,L);
        //R := [Gamma!x : x in r] where r := leftCosetRepresentatives(H, H meet GammaP);
        indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(MN, psiMN, Gamma);// : RepSys := R);
        diagN := map< N -> indMN | x :-> 
            &+([ x @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;
        
        // Fix-module by H
        H := FixedGroup(N,L);
        K := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
        indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);
       
        assert (N!L.1) @ diagN in indML;
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
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
            // compute cocycle for p
            H := FixedGroup(N,L1);
            C, qC := quo< Gamma | H>;
            //psiL1 := map< C -> Aut(L1) | g :-> Coercion(L1,N) * psiN(g @@ qC) * Coercion(N,L1) >;
            psiL1 := map< C -> Aut(L1) | g :->
                hom< L1 -> L1 | L1.1 @ Coercion(L1,N) @ psiN(g @@ qC) @ Coercion(N,L1) > 
            >;
            
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
            L1P, iotaL1, psiL1P := completion_with_precision1(L1,PL1,psiL1, m+10);
            //L1P, iotaL1 := Completion(L1, PL1 : Precision := 300); //Max(100,m*2));
            //psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
             //c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
             c := CLocalFundamentalClassSerre(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
            // inflation
            c2 := map< car<Gamma,Gamma> -> indMN | x :-> c(x[1]@qC, x[2]@qC) @@ iotaL1 @ Coercion(L1,N) @ diagN>;
            vprint GFC, 2: "test cocycle";
            vtime GFC, 2: assert testCocycleGenerators(c2, psiIndMN );
            c2 := map< Domain(c2) -> Codomain(c2) | x:-> c2(x[2]^(-1), x[1]^(-1)) >;
            
        end if;
       // here "below line" is the problem in SUnits using Raw  
        diagN:=map<US-> Codomain(diagN)| x:->PowerProduct(Base,mUS(x)) @ diagN>;
    //  diagN := mUS*diagN;
        Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *]);
        IndentPop();
    end for;

  // infinite places
    vprint GFC, 1: "modules for infinite places";
    assert &and([ IsReal(inf) : inf in InfinitePlaces(N) ]);
    psiM := map< sub<Gamma | Id(Gamma)> -> Aut(US) | sig :-> hom< US -> US | [US.i : i in [1..#Generators(US)]]> >;
    indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(US, psiM, Gamma);
    diagN := map< US -> indMN | x :-> 
            &+([ x @ psiUS(RN[i]^(-1)) @ kappaMN[i] : i in [1..#kappaMN] ]) >;
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
    // diagonal embedding of S-units
    embJN := map< US -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst]] ) >;
// embJN := map< US -> JN | x :-> &+([ PowerProduct(Base,lst[i,4](x))@ inclJN[i] : i in [1..#lst]] ) >;
 // factor out S-Units diagonally
    vtime GFC, 1: B := [g @ embJN : g in Generators(US)];
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
    G, qG := quo< Gamma | FixedGroup(N,L) >;
    psiJL := map< G -> Aut(JL) | sig :-> embLN * (sig @@ qG @ psiJN) * Inverse(embLN) >;

     vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    BL:=[];
    US_gen := [x : x in Generators(US)];
    USL_gen := [x : x in Generators(USL)];
  for i in [1..#USL_gen] do
    if USL_gen[i] in US_gen then
    Append(~BL, B[Position(US_gen, US!USL_gen[i])] @@ embLN);
     else Append(~BL,USL_gen[i] @ embJN @@ embLN);
     end if;
     end for;

/*    if Degree(L) eq Degree(N) then
                 B:= [g @@ embLN : g in B];
     else
           B := [g @ embJN @@ embLN : g in Generators(USL)];
    end if;*/
    
    CL, qCL := quo<JL | BL>;
    //GG := [sig : sig in G];
    //homBasis := [ [CL.i @@ qCL @ psiJL(sig) @ qCL : i in [1..#Generators(CL)]] : sig in GG];
    //psiCL := map< G -> Aut(CL) | sig :->
    //    hom< CL -> CL | homBasis[Index(GG, sig)] >
    //>;
    psiCL := map< G -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
    IndentPop();

    vprint GFC, 1: "compute cohomology of L";
    IndentPush();
    // compute cohomology
    // make right actions
    psiCLr := map< G -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 1: CohL := CohomologyModule(G, CL, psiCLr);
    // second cohom. group
    //vtime GFC, 1: H2L := CohomologyGroup(CohL,2);
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

     Req:=[* G,qG,Gamma,gammaC,CL,qCL,CN,qCN,embLN,CohL,CohN,primes,f1CN,thetaAll *];
     

return CohL,f1CL,comp,Req;
    end intrinsic;

intrinsic gfcCompositumcl(L::FldNum, L1::FldNum) -> ModCoho, Map, ModTupRngElt, Rec
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
    assert IsTotallyReal(N);
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
     prime:=trivialSclassless(L,L1,N);
    primes:=&cat[prime,primes];
    set:={x: x in primes};
    primes:=[x : x in set];
     seq := [p :   p in primes | #Decomposition(L1, p) eq 1];
if #seq eq 0 then
    p0:=findUndecomposedPrime(L1);
    primes:= Sort([p0] cat primes);
    else p0:=Sort(seq)[1];
    end if;

// vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);
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
    //H := FixedGroup(N,L);
    //K:=[ Kernel(VerticalJoin(Matrix([  Eltseq(US.i @ SUnitAction(mUS, psiN(h),S) - US.i)  :  i in [1..#Generators(US)]]),Transpose(D))) : h in H ] where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]);
    //K := [ Kernel(Transpose(HorizontalJoin(
    //Transpose(Matrix([  Eltseq(US.i @ SUnitAction(mUS, psiN(h),S) - US.i)  :  i in [1..#Generators(US)]])), D)))
    //: h in H ]
    //where D := DiagonalMatrix([Order(US.i) :  i in [1..#Generators(US)] ]); "is same as the next";
   
   
   
   
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

        /*
        print "compute completion, prec =", Max(100,m*2);
        NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;
        */
        //print "completion with sufficient precicion for computations up to precision ", m+10;
        vprint GFC, 2: "compute completion, prec =", m+10;
        vtime GFC, 2: NP, iotaN, psiNP := completion_with_precision(N,PN,psiN, m+10);
        LIST:=[*NP,iotaN,psiNP*];
        GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX1(N, PN, psiN,LIST, theta, m);
   //   vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX(N, PN, piN, psiN, iotaN, NP, psiNP, theta, m);  
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
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
            // compute cocycle for p
            H := FixedGroup(N,L1);
            C, qC := quo< Gamma | H>;
            //psiL1 := map< C -> Aut(L1) | g :-> Coercion(L1,N) * psiN(g @@ qC) * Coercion(N,L1) >;
            psiL1 := map< C -> Aut(L1) | g :->
                hom< L1 -> L1 | L1.1 @ Coercion(L1,N) @ psiN(g @@ qC) @ Coercion(N,L1) >
            >;

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
            L1P, iotaL1, psiL1P := completion_with_prec(L1,PL1,psiL1, m+10);
            //L1P, iotaL1 := Completion(L1, PL1 : Precision := 300); //Max(100,m*2));
            //psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
            // c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
	    if p gt 50 then
             c := CLocalFundamentalClassSerre_check(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
            else c :=CLocalFundamentalClassSerre(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
	    end if;
	    // inflation
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
    assert &and([ IsReal(inf) : inf in InfinitePlaces(N) ]);
    psiM := map< sub<Gamma | Id(Gamma)> -> Aut(US) | sig :-> hom< US -> US | [US.i : i in [1..#Generators(US)]]> >;
    indMN, psiIndMN, RN, kappaMN, projMN := inducedModule(US, psiM, Gamma);
    diagN := map< US -> indMN | x :->
            &+([ x @ psiUS(RN[i]^(-1)) @ kappaMN[i] : i in [1..#kappaMN] ]) >;
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
    // diagonal embedding of S-units
    embJN := map< US -> JN | x :-> &+([ x @ lst[i,4] @ inclJN[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 1: B := [g @ embJN : g in Generators(US)];
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
    G, qG := quo< Gamma | FixedGroup(N,L) >;
    psiJL := map< G -> Aut(JL) | sig :-> embLN * (sig @@ qG @ psiJN) * Inverse(embLN) >;

     vprint GFC, 1: "compute idele class group of L";
    IndentPush();
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

/*
H2N := CohomologyGroup(CohN,2);
    gfcId := IdentifyTwoCocycle(CohN, func< x | gammaC(x[1],x[2]) @ f1CN >);
    c := TwoCocycle(CohL, H2L.1);
    c2 := map< car< G, G> -> CL | x :-> c(<x[1],x[2]>) @@ f1CL >;
    c3 := map< car< Gamma, Gamma> -> CN | x :-> c2(x[1]@qG,x[2]@qG) @@ qCL @ embLN @ qCN>;
    c4 := func< x | c3(x) @ f1CN>;
    gfcLid := IdentifyTwoCocycle(CohN, c4);
    gfcL := [k : k in [1..#G] | k*gfcLid eq gfcId ][1] * H2L.1;
    //return CohL, f1CL, gfcL;

return CohL,f1CL,gfcL,comp,Req,H2N;
*/    
end intrinsic;




intrinsic gfcUndecomposedcl(L::FldNum, p0::RngIntElt : psiL := 0) -> ModTupRng, ModCoho, Map, ModTupRngElt, Rec
{ Computes the global fundamental class for a number field L
  in which the prime p0 is undecomposed.
  Optionally one can pass the Galois action on L as map G->Aut(L/Q).
}
    require IsTotallyReal(L) :
            "Just implemented for totally real fields!";
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
    /*
    primes:=[x[1] : x in Factorization(Discriminant(RingOfIntegers(L)))];
    choose:=[p: p in primes| #Decomposition(L,p) eq 1][1];
    primes:={p0} join {choose};
    
    */
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
    GG := [sig : sig in G];
    vtime GFC, 2: sigUS := SUnitAction(mUS, [psiL(sig) : sig in G],S);
    psiUS := map< G -> Aut(US) | sig :-> sigUS[Index(GG,sig)] >;
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
        LP, iotaL := Completion(L, PL : Precision := 1000);
        GP := [g : g in G | &and([  psiL(g)(x) in PL   : x in Generators(PL)]) ];
        GP := sub< G | GP>;
        psiLP := map< GP -> Aut(LP) | g :-> iotaL^(-1) * psiL(g) * iotaL >;
        vprint GFC, 2: "compute module";
       LIST:=[* LP,iotaL,psiLP*];
   ML, psiML, qML := compute_LPmul_modX1(L, PL, psiL, LIST, theta, m);
  //      ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, theta, m);
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
    
    
    // infinite places
    vprint GFC, 1: "modules for infinite places";
    assert &and([ IsReal(inf) : inf in InfinitePlaces(L) ]);
    psiM := map< sub<G | Id(G)> -> Aut(US) | sig :-> hom< US -> US | [US.i : i in [1..#Generators(US)]]> >;
    indML, psiIndML, RL, kappaML, projML := inducedModule(US, psiM, G);
    diagL := map< US -> indML | x :-> 
            &+([ x @ psiUS(RL[i]^(-1)) @ kappaML[i] : i in [1..#kappaML] ]) >;
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
    
    
    //psiJL := map< G -> Aut(JL) | sig :-> map< JL -> JL | x:-> &+( [ x @ projJL[i] @ lst[i,2](sig) @ inclJL[i] : i in [1..#lst]])> >;
    //time psiJL2 := map< G -> Aut(JL) | sig :-> hom< JL -> JL | [&+( [ JL.j @ projJL[i] @ lst[i,2](sig) @ inclJL[i] : i in [1..#lst]]) : j in [1..#Generators(JL)]]> >;
    /*
    psiJLr := map< G -> Aut(JL) | g :-> psiJL(g^(-1)) >;
    CohJL := CohomologyModule(G, JL, psiJLr);
    H2JL := CohomologyGroup(CohJL,2);
    f1JL := map< JL -> RSpace(Integers(),Dimension(CohJL)) |
        x:-> Eltseq(x),
        y:-> JL!Eltseq(y)
    >;
    */
    gamma := map< car<G, G> -> JL | x :-> &+([ x @ lst[i,4] @ inclJL[i]  : i in [1..#lst] ]) >;
    //gfcId := IdentifyTwoCocycle(CohJL, func< x | gamma(x[1],x[2]) @ f1JL >);
    IndentPop();
    vprint GFC, 1: "Time:", Cputime(t);
    t := Cputime();
    
    vprint GFC, 1: "compute idele class group of L";
    IndentPush();
    // diagonal embedding of S-units
    embJL := map< US -> JL | x :-> &+([ x @ lst[i,3] @ inclJL[i] : i in [1..#lst]] ) >;
    // factor out S-Units diagonally
    vtime GFC, 2: B := [g @ embJL : g in Generators(US)];
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
    
return CohL, f1CL, gfcId,comp ;
//return H2L,CohL, f1CL, gfcId, comp;
end intrinsic;



///////////This is to check the gfcCompositmcl/////////////////////Modified///////////



intrinsic trivialSClassNumberPrimes_check(L,L1,N : primes := []) -> SeqEnum
{ Compute a sequence of primes such that the S-class number of
  all subfields of L is trivial. Optionally specify a set of primes
  which will be included in S. }
    //print "compute subfields";
    subL := [* L, L1,N *];
    vprintf GFC, 2: "%o subfields ", #subL;
    for F in subL do
        vprintf GFC, 2: ".";
     //   F := sub[1];
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

intrinsic trivialSclassless(L,L1,N)->.{}
OL:=MaximalOrder(L);
OL1:=MaximalOrder(L1);
ON:=MaximalOrder(N);
set:=[OL,OL1,ON];
P:=[p: p in [1..500]| IsPrime(p)];
c,mc:=ClassGroup(L:Bound:=BachBound(L));
c1,mc1:=ClassGroup(L1:Bound:=BachBound(L1));
C,mC:=ClassGroup(N:Bound:=BachBound(N));
Cl:=[<c,mc>,<c1,mc1>,<C,mC>];
primes:=[];
 if #c eq 1 and #c1 eq 1 and #C eq 1 then
   return primes;
   else
for p in P do
    if &meet[{#quo<Cl[i,1]| [x[1]@@ Cl[i,2]: x in Decomposition(set[i],p)]>}: i in [1..3]] eq {1} then
    Append(~primes,p);
    break p;
    end if;
    end for;
 return primes;
 end if;
end intrinsic;


intrinsic directSum(S::[GrpAb]) -> GrpAb, SeqEnum, SeqEnum
   {The direct sum of the abelian groups in S followed by the 
   sequences of canonical inclusions and projections, respectively.}
   G := AbelianGroup([]);
   Ggens := [ ];
   projs := [ ];
   for k in [1..#S] do
      G, i1, i2, p1, p2 := DirectSum(G,S[k]);
      Ggens := [ [ i1(x) : x in Ggens[i] ] : i in [1..k-1] ];
      Append(~Ggens,[ i2(S[k].i) : i in [1..Ngens(S[k])] ]);
      projs := [ hom< G -> S[i] | x :-> projs[i](p1(x)) >
         : i in [1..k-1] ] cat [ p2 ];
   end for;
   f := func<x, k|&+[ Eltseq(x)[i]*Ggens[k][i] : i in [1..Ngens(S[k])]]>;
   return G, 
      [ hom< S[k] -> G | [f(S[k].i, k) : i in [1..Ngens(S[k])]]> :
          k in [1..#S] ], projs;
end intrinsic;

/*
intrinsic RelativeBasis(K::RngPad, k::FldPad) -> []
  {The k-basis of K, compatible with repeated Eltseq}
  B := Basis(K);
  if CoefficientRing(K) eq k then
    return B;
  else
    b := RelativeBasis(CoefficientRing(K), k);
    return [i*j : j in b, i in B];
  end if;
end intrinsic;*/

intrinsic AbsoluteBasis(K::RngPad) -> []
  {A Zp basis for K}
  return RelativeBasis(K, PrimeRing(K));
end intrinsic;


intrinsic NormalBasisElement_check(OL :: RngOrd, h :: Map : rand := false) -> RngOrdElt
{}
    local G, b, D, found;

    G := Domain(h);

    if not rand then
        for b in Basis(OL) do
            D := Matrix([ ElementToSequence( h(g)(b) ) : g in G ]);
            if Determinant(D) ne 0 then
                return OL!b;  
            end if; 
        end for;
    end if;

    found := false;
    while  not found  do
        b := OL ! [ Random(3) : i in [1..Degree(OL)] ];
        D := Matrix([ ElementToSequence( h(g)(b) ) : g in G ]);
        if Determinant(D) ne 0 then
           return OL!b;
        end if;
    end while;
    
    if not found then
        error "ERROR: No normal basis element found!!!";
    end if;
end intrinsic;





intrinsic maximal_unram_subext_simple(OL)->.{}
    local Zp, OK;
    
    if Type(OL) eq RngPad then
        Zp := pAdicRing(OL);
    else
        Zp := pAdicField(OL);
    end if;
    if isUnramified(OL,Zp) then
        OK := OL;
    elif isTotallyRamified(OL,Zp) then
        OK := Zp;
    else
        OK := OL;
        while AbsoluteDegree(OK) gt AbsoluteInertiaDegree(OK) do
            OK := BaseRing(OK);
        end while;
        assert AbsoluteDegree(OK) eq AbsoluteInertiaDegree(OK);
    end if;
    // habe nun Erweiterungen OL/OK/Zp 
    // mit OL/OK voll verzweigt und OK/Zp unverzweigt
    assert isTotallyRamified(OL, OK);
    assert isUnramified(OK, Zp);
    // OK soll "einfache" Erweiterung sein
    assert Degree(OK) eq Degree(OK, Zp);
    
    return OK;
end intrinsic;






//////////////////checking/////////////
//
//




intrinsic gfcCompositum_relative_check_update(L::FldNum, L1::FldNum, prec:: RngIntElt) -> ModCoho, Map, ModTupRngElt, Rec
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
  N:= AbsoluteField(N1);
//  N:=OptimisedRepresentation(AbsoluteField(N1));
    assert IsTotallyReal(N);
    ON := RingOfIntegers(N);
    Gamma, _ ,psiN := AutomorphismGroup(N);
    psiN := map< Domain(psiN) -> Codomain(psiN) | x :-> psiN(x^(-1)) >;
    Gamma1 := AutomorphismGroup(N1);
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


//   US0 := US;
//   mUS0 := mUS;
   
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



 /*
    fac := Factorization(p*ON);
        PN :=fac[1,1];
       // piN := UniformizingElement(PN);
        vprint GFC, 2: "compute lattice";
        t := Cputime();
        if RamificationIndex(PN) eq 1 then
            theta := ON!1;
            m := 0;
        else
	
	//if #Decomposition(BaseField(L),p) eq 1 then
	   theta, m := lattice_check(fac[1,1], psiN);
       if #Decomposition(BaseField(L),p) gt 1 then
      
	   for i in [1..#fac] do
               theta1, m1 := lattice_check(fac[i,1], psiN);
                if m1 lt m then
                    theta := theta1;
                    m := m1;
		    PN := fac[i,1];
                   // piN := UniformizingElement(PN);
		end if;
            end for;
	    end if;
        end if;
        Append(~thetaAll, ON!theta);
        vprint GFC, 2: "Time:", Cputime(t);
*/
 //NP, iotaN := relative_completion_check(N,N1,BaseField(N1),p,100);
  NP, iotaN := relative_completion_check(N,N1,BaseField(N1),p,prec);
  fac := Factorization(p*ON);
 // PN:=[fac[i,1]: i in [1..#fac]|  Valuation(Generators(fac[i,1])[2] @ iotaN) eq 1][1];
 if #fac eq 1 then
   PN :=fac[1,1];
 else
    // if there is no principal ideal
    fac_P := [fac[i,1]: i in [1..#fac]|  Valuation(Generators(fac[i,1])[2] @ iotaN) eq 1];
  if #fac_P ge 1 then
     PN := fac_P[1];
   else PN := Factorisation(p*ON)[1,1];
   end if; 
   end if;

if RamificationIndex(PN) eq 1 then
        theta := ON!1;
	m := 0;
else 	
 //theta, m := lattice_check(PN, psiN_abs);
   theta, m := lattice_check(PN, psiN); 
 end if;

  Append(~thetaAll, ON!theta);

  GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;



  

/*
    NP, iotaN := relative_completion_check(N,N1,BaseField(N1),p,100);
    P_N := UniformizingElement(NP) @@ iotaN;
    // " Factorisation may cost";
    fac := Factorisation(P_N*ON);
    fac_p := [fac[i]: i in [1..#fac]| Generator(fac[i,1] meet Integers()) eq p];
  // "in search of prime ideals associated to pAdicField";
 
 
 if #fac_p ge 1 then 
      PN := fac_p[1,1];
    else 
      PN := Factorisation(p*ON)[1,1];
   end if;
if RamificationIndex(NP) eq 1 then
           theta := ON!1;
            m := 0;
      else
         theta, m := lattice_check(PN, psiN);
	  if m gt NP`DefaultPrecision then
             NP, iotaN := relative_completion_check(N,N1,BaseField(N1),p,Max(100,m*2));
             P_N := UniformizingElement(NP) @@ iotaN;
             PN := Factorisation(P_N*ON)[1,1];
             theta, m := lattice_check(PN, psiN);
            end if;
end if;    
*/
// NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
 // Append(~thetaAll, ON!theta);   
  // vprint GFC, 2: "Time:", Cputime(t);

 // GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
   //     GammaP := sub< Gamma | GammaP>;
     //   psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;

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
        diagN := map< N -> indMN | x :->
            &+([ x @ psiN(RN[i]^(-1)) @ iotaN @ qMN @ kappaMN[i] : i in [1..#kappaMN] ]) >;

H := AutomorphismGroup(N1,L);
// H := AutomorphismGroup(N,L);

K := [ Kernel(Transpose(HorizontalJoin(
            Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
        : h in H ]
        where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
        indML := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in K]);

        assert (N1 !L.1) @ diagN in indML;
 if p ne p0 then
            // trivial cocycle for this
            // "Here may be the problem because Aut(N1 or N) ";
            c2 := map< car<Gamma, Gamma> -> indMN | x :-> Zero(indMN) >;
        else
            vprint GFC, 2: "compute cocycle, prec =", m;
            // compute cocycle for p


      HL1 := AutomorphismGroup(N1, L1_abs);

     // C, qC := quo< Gamma | HL1>;
      C, qC := quo< Gamma1 | HL1>;
      GL1 :=AutomorphismGroup(L1);
      _,phiL1 :=IsIsomorphic(GL1,C);
            //psiL1 := map< C -> Aut(L1) | g :-> Coercion(L1,N) * psiN(g @@ qC) * Coercion(N,L1) >;
	     //psiL1 := map< C -> Aut(L1) | g :->hom< L1 -> L1 | L1.1 @ Coercion(L1,N1) @ psiN(g @@ qC) @ Coercion(N,L1) > >;
           // psiL1 := map< C -> Aut(L1_abs) | g :-> hom< L1_abs -> L1_abs | L1_abs.1 @ Coercion(L1_abs,N) @ psiN(g @@ qC) @ Coercion(N,L1_abs) > >;
            psiL1 := map< GL1 -> Aut(L1_abs) | g :-> hom< L1_abs -> L1_abs | L1_abs.1 @ Coercion(L1_abs,N) @ psiN(g@phiL1 @@ qC) @ Coercion(N,L1_abs) > >;
              
            // compute ML1
            KL1 := [ Kernel(Transpose(HorizontalJoin(
                Transpose(Matrix([  Eltseq(indMN.i @ psiIndMN(h) - indMN.i)  :  i in [1..#Generators(indMN)]])), D)))
                : h in HL1 ]
                where D := DiagonalMatrix([Order(indMN.i) :  i in [1..#Generators(indMN)] ]);
            indML1 := &meet([sub<indMN | [indMN!Eltseq(b)[1..#Generators(indMN)] :  b in Basis(k)]> : k in KL1]);
           // psiIndML1 := map< C -> Aut(indML1) |
              //  sig :-> Coercion(indML1, indMN)*psiIndMN(sig @@ qC)*Coercion(indMN,indML1) >;

	    psiIndML1 := map< GL1 -> Aut(indML1) |
                sig :-> Coercion(indML1, indMN)*psiIndMN(sig@phiL1 @@ qC)*Coercion(indMN,indML1) >;

            // compute completion of L1
            //PL1 := Factorization(p*RingOfIntegers(L1))[1,1];
	    // since there is onle one prime ideal
            PL1:= Factorization(p*RingOfIntegers(L1_abs))[1,1];

            //print "completion with sufficient precicion for computations up to precision ", m+10;
            vprint GFC, 2: "compute completion, prec =", m+10;
            L1P, iotaL1 := relative_completion_check(AbsoluteField(L1),L1,BaseField(L1),p, prec); //Max(100,m*2));
           // psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            psiL1P := map< GL1 -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
            // c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
          if p gt 50 then
	  c := CLocalFundamentalClassSerre_check(L1P, PrimeField(L1P), m+5 : psi := psiL1P);
          //c := CLocalFundamentalClassSerre_check(L1P, BaseField(L1P), m+5 : psi := psiL1P);
          else
          c := CLocalFundamentalClassSerre_check(L1P, PrimeField(L1P), m+5 : psi := psiL1P);
	  //c := CLocalFundamentalClassSerre(L1P, BaseField(L1P), m+5 : psi := psiL1P);
           end if;
            // inflation
	      //c2 := map< car<Gamma,Gamma> -> indMN | x :-> c(x[1]@qC, x[2]@qC) @@ iotaL1 @ Coercion(L1,N) @ diagN>;
            c2 := map< car<Gamma1,Gamma1> -> indMN | x :-> c(x[1]@qC@@phiL1, x[2]@qC@@phiL1) @@ iotaL1 @ Coercion(L1,N) @ diagN>;
            vprint GFC, 2: "test cocycle";
            // have to fit this for relative case
	  //  vtime GFC, 2: assert testCocycleGenerators(c2, psiIndMN );
            c2 := map< Domain(c2) -> Codomain(c2) | x:-> c2(x[2]^(-1), x[1]^(-1)) >;
 end if;

        diagN := mUS0*diagN;
        Append(~lst, [* indML, indMN, psiIndMN, diagN, c2 *]);
        IndentPop();
    end for;

    vprint GFC, 1: "modules for infinite places";

  /////uncheck here

// Gamma1 :=sub< FixedGroup(N,BaseField(L)) | AutomorphismGroup(N1)>;
//  Gamma1 := AutomorphismGroup(N1);
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
    //G, qG := quo< Gamma1 | AutomorphismGroup(N1,L) >; "changed to work on G";
     G, qG := quo< Gamma1 | FixedGroup(N,L) >;
  /* 
    GL:=AutomorphismGroup(L);
   _,phiL:=IsIsomorphic(GL,G);
   psiJL := map< GL -> Aut(JL) | sig :-> embLN * (sig@phiL @@ qG @ psiJN) * Inverse(embLN) >;

   vtime GFC, 1: B := [g @ embJN @@ embLN : g in Generators(USL0)];
    CL, qCL := quo<JL | B>;
   psiCL := map< GL -> Aut(CL) | sig :-> Inverse(qCL)*psiJL(sig)*qCL >;
   psiCLr := map< GL -> Aut(CL) | g :-> psiCL(g^(-1)) >;
    vtime GFC, 1: CohL := CohomologyModule(GL, CL, psiCLr);


 */

   



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
      //    c2 := map< car< GL, GL> -> CL | x :-> c(<x[1],x[2]>) @@ f1CL >;
	c3 := map< car< Gamma1, Gamma1> -> CN | x :-> c2(x[1]@qG,x[2]@qG) @@ qCL @ embLN @ qCN>;
      //c3 := map< car< Gamma1, Gamma1> -> CN | x :-> c2(x[1]@qG@@phiL,x[2]@qG@@phiL) @@ qCL @ embLN @ qCN>;
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
