/*
 * Test suite
 * 
 * UNCOMMENT THE PASSING TESTS
 */

:- begin_tests(pp_tema).

% setters - 0.5p

test(setter) :-
	set( [[[port, 1], [a, 1], [b, 2]], [[port, 1], [a, 3], [b, 2]]] , a, 2, R),
	R == [[[port, 1], [a, 2], [b, 2]], [[port, 1], [a, 2], [b, 2]]].

test(setter2) :-
	set( [[[a, 1], [b, 2]], [[a, 2], [b, 3]]], a, x, R),
	R == [[[a, x], [b, 2]], [[a, x], [b, 3]]].


% rmDup - 0.5p

test(rmDup) :-
	rmDup([1, 2, 2, 4, 2, 5, 9], R),
	R ==  [1,       4, 2, 5, 9].


% rmVal - 0.5p

test(rmVal) :-
	rmVal([1, 2, 2, 4, 2, 5, 9], 2, R),
	R ==  [1,       4,    5, 9].


% intCf - 1.0p

test(intCf1, [nondet]) :-
	intCf([[a, 1  ], [b, 2  ], [c, any], [d, any]],
	      [[a, any], [b, any], [c, 1  ], [d, 2  ]], R),
	R ==  [[a, 1  ], [b, 2  ], [c, 1  ], [d, 2  ]].

test(intCf2, [nondet]) :-
	intCf([[a, 1  ], [b, 2], [c, any]],
	      [[a, any], [b, 2], [c, 3  ]], R),
	R ==  [[a, 1  ], [b, 2], [c, 3  ]].

test(intCf3, [nondet]) :-
	intCf([[a, 1], [b, 3]],
	      [[a, 2], [b, 3]], R),
	R == cvoid.


% inter - 1.0p

test(inter1) :-
	inter([[[a, 1], [b, 2  ]] , [[a, 2], [b, 2]]],
	      [[[a, 1], [b, any]]], R),
	R ==  [[[a, 1], [b, 2  ]]].

test(inter2) :-
	inter([[[a, 1], [b, any]] , [[a, any], [b, 2]]],
	      [[[a, 1], [b, 2  ]]], R),
	R ==  [[[a, 1], [b, 2  ]]].

test(inter3) :-
	inter([[[a, 1]], [[a, 3]]],
	      [[[a, 2]]], R),
	R ==  [].

test(inter4) :-
	inter([[[a, 1], [b, 1]], [[a, 2], [b, 2]]], [[[a, 3], [b, 3]]], R),
	R == [].


% modify - 1.0p

test(modify) :-
	modify([[[a, 1], [b, 2]], [[a, 2], [b, 3]]], [[a, 9]], R),
	R ==   [[[a, 9], [b, 2]], [[a, 9], [b, 3]]].


% subsetCf - 1.0p

test(subsetCf1) :- subsetCf([[a, 1], [b, 2]], [[a, 1], [b, any]]).

test(subsetCf2) :- subsetCf([[a, 1]], [[a, 1]]).

test(subsetCf3) :- \+ subsetCf([[a, 1]], [[a, 2]]).


% subset - 1.0p

test(subset1) :-
	 subset([[[a, 1], [b, 1  ]], [[a, 2], [b, 3]]],
	        [[[a, 1], [b, any]], [[a, 2], [b, 3]]]).

test(subset2) :-
	\+ subset([[[a, 1], [b, 1]], [[a, 2], [b, 3]]],
	          [[[a, 1], [b, 2]], [[a, 2], [b, 3]]]).

test(subset3) :- subset([[[a, 1]]], [[[a, 1]]]).


% reachAll - 1.5p
/*
test(reach1) :-
	reachAll([[[port, p1], [dst, any]]], R),
	R == [[[[port, p2], [dst, any]]],
		  [[[port, p3], [dst, any]]],
		  [[[port, p1], [dst, any]]]].

test(reach2) :-
	reachAll([[[port, p10], [dst, any]]], R),
	R == [[[[port, p11], [dst, any]]],
		  [[[port, p12], [dst, any]]],
		  [[[port, p13], [dst, any]]]].

test(reach3) :-
	reachAll([[[port, p30], [dst, p39]]], R),
	R = [[[[port, p31], [dst, p39]]]].

test(reach3b) :-
	reachAll([[[port, p30], [dst, p33]]], R),
	R = [[[[port, p31], [dst, p33]]],
		 [[[port, p32], [dst, p33]]],
		 [[[port, p33], [dst, p33]]]].

test(reach4) :-
	reachAll([[[port, p40], [dst, p41]]], R),
	R = [[[[port, p41], [dst, p41]]],
		 [[[port, p42], [dst, p49]]],
		 [[[port, p49], [dst, p49]]]].
*/

% loop - 2.0p
/*
test(loop1) :-
	loop([[[port, p1], [dst, any]]]).

test(loop2) :-
	\+ loop([[[port, p10], [dst, any]]]).
*/

:- end_tests(pp_tema).