
declare verbose GFC, 2;


import "localModule.m"  : lattice_generator_theta, lattice, find_included_P_power_absolute,
                            compute_LPmul_modX;

import "localModule.m" : completion_with_prec;


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


intrinsic gfcUndecomposed(L::FldNum, p0::RngIntElt : psiL := 0) -> ModCoho, Map, ModTupRngElt, Rec
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
        ML, psiML, qML := compute_LPmul_modX(L, PL, UniformizingElement(PL), psiL, iotaL, LP, psiLP, theta, m);
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
    
    return CohL, f1CL, gfcId, comp;
end intrinsic;





intrinsic gfcCompositum(L::FldNum, L1::FldNum) -> FldNum, ModCoho,ModCoho
{ Given an arbitrary Galois extension L/Q and a cyclic extension L1/Q
  of the same degree, this method computes then global fundamental
  class of L/Q.
}
    
    require IsCyclic(L1) and Degree(L) eq Degree(L1) :
            "Second number field must be cyclic and of the same degree!";
    
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
    if #seq eq 0 or seq[1] gt 50 then
        p0 := findUndecomposedPrime(L1);
        primes := Sort([p0] cat primes);
    else
        p0 := Sort(seq)[1];
    end if;
    // trivial S-class numbers
    vtime GFC, 2: primes := trivialSClassNumberPrimes(N : primes := primes);
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
        
        /*
        print "compute completion, prec =", Max(100,m*2);
        NP, iotaN := Completion(N, PN : Precision := Max(100,m*2));
        GammaP := [g : g in Gamma | &and([  psiN(g)(x) in PN   : x in Generators(PN)]) ];
        GammaP := sub< Gamma | GammaP>;
        psiNP := map< GammaP -> Aut(NP) | g :-> iotaN^(-1) * psiN(g) * iotaN >;
        */
        //print "completion with sufficient precicion for computations up to precision ", m+10;
        vprint GFC, 2: "compute completion, prec =", m+10;
        vtime GFC, 2: NP, iotaN, psiNP := completion_with_prec(N,PN,psiN, m+10);
        GammaP := Domain(psiNP);
        vprint GFC, 2: "compute module";
        vtime GFC, 2: MN, psiMN, qMN := compute_LPmul_modX(N, PN, piN, psiN, iotaN, NP, psiNP, theta, m);
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
            L1P, iotaL1, psiL1P := completion_with_prec(L1,PL1,psiL1, m+10);
            //L1P, iotaL1 := Completion(L1, PL1 : Precision := 300); //Max(100,m*2));
            //psiL1P := map< C -> Aut(L1P) | g :-> iotaL1^(-1) * psiL1(g) * iotaL1 >;
            // cocycle C x C -> L1P
            //SetVerbose("CocycleLFC", 1);
            c := CocycleLFC(L1P, pAdicField(L1P), m+5 : psi := psiL1P);
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
    /*projJN := [ hom< JN -> lst[k,2] | 
        [ Index(seq,i) eq 0 select lst[k,2]!0 else lst[k,2].(Index(seq,i))  : i in [1..#Generators(JN)]] 
        >
        where seq := [Index(Eltseq(inclJN[k](lst[k,2].i)),1) : i in [1..#Generators(lst[k,2])]]
        : k in [1..#lst]];
    */
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
    
    vprint GFC, 1: "Time for idele class group of N:", Cputime(t);
    t := Cputime();
    
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
    // recompute projections
    //time projJL := [ hom< Domain(p) -> Codomain(p) | [ p(JL.i) : i in [1..#Generators(JL)]] >  : p in projJL ];
    /*projJL := [ hom< JL -> lst[k,1] | 
        [ Index(seq,i) eq 0 select lst[k,1]!0 else lst[k,1].(Index(seq,i))  : i in [1..#Generators(JL)]] 
        >
        where seq := [Index(Eltseq(inclJL[k](lst[k,1].i)),1) : i in [1..#Generators(lst[k,1])]]
        : k in [1..#lst]];
    */
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
        primes := primes, US := USL, mUS := mUSL,
        //kappaInf := kappaML, RepInf := RL, inclJL := inclJL,
        inclUSJL := inclUSJL,
        theta := thetaAll >;
    
return N,CohN,CohL;
//H2N:=CohomologyGroup(CohN,2);
end intrinsic;



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


intrinsic latticeGlob(L::FldNum : psi := 0) -> RngOrd
{ Compute the lattice scrL as in [HS132,§3.1]. }
    
    if psi cmpeq 0 then
        G,_, psi := AutomorphismGroup(L);
        psi := map< Domain(psi) -> Codomain(psi) | x :-> psi(x^(-1)) >;
    else
        G := Domain(psi);
    end if;
    
    OL := RingOfIntegers(L);
    primes :=  [f[1] : f in fac] where fac := Factorization(Discriminant(OL));
    
    X := [];
    for p in primes do
        P := Factorization(p*OL)[1,1];
        GP := DecompositionGroup(P);
        F := ( GP eq G select Rationals() else
            [s[1] : s in Subfields(L, Integers()!(Degree(L)/#GP)) | FixedGroup(L,s[1]) eq GP][1]);
        assert GP eq FixedGroup(L,F);
        
        L1 := RelativeField(F, L);
        OL1 := RingOfIntegers(L1);
        P1 := ideal<OL1 | [L!b : b in Generators(P)]>;
        P1 := Factorization(P1)[1,1];
        
        psiL1 := map< GP -> Aut(L1) | g :-> Coercion(L1,L)*psi(g)*Coercion(L,L1)>;
        theta, m := lattice(P1, UniformizingElement(P1), psiL1);
        
        // X_p = OF[GP]*theta
        OF := RingOfIntegers(F);
        if Type(OF) eq RngInt then
            erz := [psiL1(g)(theta) : g in GP];
        else
            erz := [b*psiL1(g)(theta) : g in GP, b in Basis(OF)];
        end if;
        //Append(~X, Lattice( Matrix( [ [Integers()!y : y in Eltseq(OL!L!x)] : x in erz])));
        Append(~X, sub<OL |   [OL!L!x : x in erz]>);
    end for;
    
    scrL := &meet(X);
    return scrL;
end intrinsic;


// should use devide and conquer method
function finiteSum(M, k)
    N, i1,i2 := DirectSum(M,M);
    iota := [i1,i2];
    for i in [3..k] do
        N, j, i3 := DirectSum(N, M);
        iota := Append([m*j : m in iota], i3);
    end for;
    
    return N, iota;
end function;

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



intrinsic leftCosetRepresentatives(G::GrpPerm, H::GrpPerm : RepSys := 0) -> SeqEnum
{ Compute a system of representatives of G/H. }
    
    if RepSys cmpeq 0 then
        R := [Id(G)];
        for g in [g : g in G | g ne Id(G)] do
            if not &or([g in tau*H : tau in R]) then
                Append(~R, g);
            end if;
        end for;
    else
        // first use representatives given by RepSys
        R := [];
        for g in [g : g in RepSys ] do
            if not &or([g in tau*H : tau in R]) then
                Append(~R, g);
            end if;
        end for;
        RepSys := R;
        
        for g in [g : g in G | g ne Id(G)] do
            if not &or([g in tau*H : tau in R]) then
                Append(~R, g);
                // add also those that arrise by multiplying with
                // elements in given Rep.System
                
                for sig in [g*sig : sig in RepSys ] do
                    if not &or([sig in tau*H : tau in R]) then
                        Append(~R, sig);
                    end if;
                end for;
            end if;
        end for;
        
    end if;
    
    return R;
end intrinsic;


intrinsic testCocycleGenerators(gamma::Map, actCodom::Map) -> BoolElt
{ Test the cocycle conditions on the generators of the group. }
    
    local G, actB, seq, B, gens;
    
    G := Component(Domain(gamma),1);
    B := Codomain(gamma);
    if Type(Domain(actCodom)) ne SetCart then
        assert G eq Domain(actCodom);
        actB := map< car<G, B> -> B | x :-> actCodom(x[1])(x[2]) >;
    else
        actB := actCodom;
    end if;
    
    gens := Generators(G) join {Id(G)};
    
    if Type(B) in {RngPad, FldPad} then
        return { Valuation(gamma(sig*tau, rho)*gamma(sig,tau)-
                 actB(sig,gamma(tau,rho))*gamma(sig,tau*rho))
                : sig in gens, tau in gens, rho in gens};
        
    elif Type(B) in {ModTupRng} then
        seq := [ gamma(sig*tau, rho)+gamma(sig,tau) -
               ( actB(sig,gamma(tau,rho))+gamma(sig,tau*rho) )
               : sig in gens, tau in gens, rho in gens];
        
        return &and([ B!ElementToSequence(x) eq Zero(B) : x in seq ]);
    else
        seq := [ gamma(sig*tau, rho)*gamma(sig,tau) -
               ( actB(sig,gamma(tau,rho))*gamma(sig,tau*rho) )
               : sig in gens, tau in gens, rho in gens];
        
        return &and([ x eq Zero(B) : x in seq ]);
    end if;
end intrinsic;






