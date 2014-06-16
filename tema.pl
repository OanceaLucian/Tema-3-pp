/*
 * Compact flows are represented as lists of bindings, and each binding
 * is actually a list of two elements, the first being the field name
 * and the second - the expected value or the 'any' atom.
 *
 * A special compact flow is 'cvoid' - the null compact flow.
 * While the rest of the compact flows are lists with the length equal
 * with the number of fields in the problem, the null flow is only this
 * atom.
 *
 * Flows are represented by lists meaning reunions of compact flows.
 *
 * Example 1:
 * The flow [[[src, 1], [dst, 3]], [[src, 2], [dst, 3]]]
 * means the reunion of the two compact flows, each
 * having the destination field set to 3.
 *
 * Example 2:
 * The flow []
 * is the null flow.
 *
 * Please manually compile Prolog if the PlUnit module is not available
 * under linux (uninstall the one from the package manager first to be
 * sure it doesn't trigger any conflicts).
 *
 *  git clone git://prolog.cs.vu.nl/home/pl/git/pl.git
 *  cd pl
 *  ./configure # Answer 'yes' at the first question, then '3' at the second
 *  make
 *  sudo make install
 *
 * And then, inside the interpreter:
 * :- ['tema.pl', 'checker.plt']
 * :- run_tests.
 *
 * 
 * Under Windows, the SWI-Prolog program has PlUnit built-in.
 */


/*
 * setCf(+cflow, +header_name, +value, -cflow_out)
 *
 * Overwrite a field value in a compact flow
 */
setCf([], _, _, []).
setCf([[H,_]|T],H,O,[[H,O]|T1]):- setCf(T,H,O,T1),!.
setCf([[X,V]|T],H,O,[[X,V]|T1]):-dif(X,H),setCf(T,H,O,T1).

/*
 * set(+flow, +header_name, +value, -flow_out)
 *
 * Overwrite a field value in a flow
 */
mymap(_,[],_,_,[]).
mymap(P,[H1|T1],H,V,[H2|T2]):-call(P,H1,H,V,H2),mymap(P,T1,H,V,T2).
 set(F,H,V,NF):- mymap(setCf,F,H,V,NF),!.


/******************** Misc list functions ******************************/
/*
 * rmDup(+in_list, -out_list)
 *
 * Removes duplicates from a list. 
 *
 * The membership test to the rest of the set is the one present in the member/2
 * implementation.
 * The cut below is to simplify the tests (no choicepoint means deterministic testing).
 */
rmDup([], []).
rmDup([H|T],L):- member(H,T),!,rmDup(T,L).
rmDup([H|T],[H|L]):- rmDup(T,L).

/*
 * rmVal(+in_list, +in_term, -out_list)
 *
 * Removes all instances of the in_term from the in_list
 */
rmVal([],_,[]):-!.
rmVal([H|T1], H, T2):-rmVal(T1,H,T2),!.
rmVal([H|T],A,[H|R]):- dif(H,A),rmVal(T,A,R).


/******************** Intersection ******************************/
/*
 * intCf(+flow1, +flow2, -out)
 *
 * Compact flow intersection. If the flows are disjoint, the
 * 'cvoid' atom is returned.
 */
intCf(_,cvoid,cvoid):-!.
intCf(cvoid,_,cvoid):-!.
intCf([],[],[]):-!.
intCf([[H,any]|T1], [[H,any]|T2], [[H,any]|T3]):-intCf(T1,T2,T3),!.
intCf([[H,V]|T1], [[H,V]|T2], [[H,V]|T3]):-intCf(T1,T2,T3),!.
intCf([[H,V]|T1], [[H,any]|T2], [[H,V]|T3]):-intCf(T1,T2,T3),!.
intCf([[H,any]|T1], [[H,V]|T2], [[H,V]|T3]):-intCf(T1,T2,T3),!.

intCf([[H,V1]|_], [[H,V2]|_], R):-V1\=V2,R=cvoid,!.

/*
 * inter(+flow1, +flow2, -flow_out)
 *
 * Flow intersection.
 * If the flows are disjoint, the [] is returned.
 */
inter(_, [], []):-!.
inter([],_,[]):-!.
inter([H1|T],[H2|T1],[F|T2]):- intCf(H1,H2,Rp),Rp\=cvoid,F=Rp,inter(T,T1,T2),!.
inter([H1|_],[H2|_],[]):- intCf(H1,H2,Rp),Rp==cvoid,!.




/******************** Overwriting ******************************/
/*
 * modify(+flow_in, +new_bindings, -flow_out)
 *
 * Overwrite the bindings to the new values.
 * This will be used in implementing over network functions
 */

modify(F,[],F):-!.
modify(H,[[H1,V]|_],Rp):- set(H,H1,V,R),Rp=R,!.

/******************** Subset ******************************/
/*
 * subsetCf(+cflow1, +cflow2)
 *
 * This predicate returns true if cflow1 is a subset of cflow2
 */
subsetCf([], []):- !.
subsetCf([[H,V]|T1], [[H,V]|T2]):-subsetCf(T1,T2),!.
subsetCf([[H,_]|T1], [[H,any]|T2]):-subsetCf(T1,T2),!.


/*
 * subset(+flow1, +flow2)
 *
 * This predicate returns true if flow2 fully contains flow1.
 */
subset([], []):-!.
subset([H1|T1],[H2|T2]):- subsetCf(H1,H2),subset(T1,T2).


/******************** Rule generation *************************/

/*
 * genericRule(M, F, O).
 *
 * A basic unit of our model. These may be instantiated manually
 * (as in the test below) or being asserted from a wireRule.
 *
 * The tree parameters of a generic rule are
 * Match - for a rule to match an inbound flow, the flow
 *		has to be a subset of this parameter (also a flow).
 *
 * Filter -  after a rule matches, the inbound flow is intersected
 *		with the filter flow, so that some compact flows may be dropped
 *
 * Ovr - a filtered flow should then have some values overwritten.
 *
 * ------------
 * In this example we are using two fields for each flow:
 * port - the physical port where the packet is placed
 * dst - the destination of the packet
 */

/*
 * A wireRule(R1, R2) receives two ports (physical endpoints)
 * and matches the traffic coming to the first endpoint (R1)
 * and overwrites the field 'port' to R2, representing the
 * traffic on the other endpoint.
 *
 * wireRules are instantiated by the testing suite.
 */

/*
 * Write a predicate to deduce a genericRule from a wireRule
 */

genericRule(_, _, _) :- wireRule(_, _).

/*
 * nf(+flow_in, -flow_out)
 *
 * Apply a matching network function on the flow and output the results.
 */
nf(_, _).

/******************** Reachability *************************/
/*
 * reach(+src, -out, aux)
 *
 * The 'aux' term of the predicate may be used in your implementation
 * as you wish. The initial 'reach' call will set it to the empty list.
 *
 * The 'out' term should return, each time, a flow which is derived by applying
 * network functions over the input flow or over other results.
 */
reach(_, _, _).

/*
 * reachAll(+src, -out)
 *
 * Compute all the reachable flows starting with the reachAll.
 *
 * hint: findAll
 */
reachAll(_, _).

/*
 * Loop detect
 *
 * Returns 'true' if there's a cyclic path inside the connected
 * component of the graph that contains the flow
 */
loop(_).

/*
 *
 * DO NOT EDIT THE FILE BELOW THIS POINT
 *
 */

:- style_check(-discontiguous).

/******************** Ring sample network *************************/
wireRule(p1, p2).
wireRule(p2, p3).
wireRule(p3, p1).

/******************** Bus sample network *************************/
wireRule(p10, p11).
wireRule(p11, p12).
wireRule(p12, p13).

/******************** Star sample network *************************/
wireRule(p20, p21).
wireRule(p20, p22).
wireRule(p20, p23).
wireRule(p20, p24).

/******************** Firewalled server *************************/
wireRule(p30, p31).
genericRule([[[port, p31], [dst, any]]], [[[port, any], [dst, p33]]], [[port, p32]]).
wireRule(p32, p33).

/******************** Proxy demo *************************/
wireRule(p40, p41).
genericRule([[[port, p41], [dst, any]]], [[[port, any], [dst, p41]]], [[port, p42], [dst, p49]]).
wireRule(p42, p49).

:- load_test_files([]).