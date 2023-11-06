% NOTE: This is intended to be used with the Ciao Prolog system

% :- module(rb2, _, [bf, modes]).
% :- module(rb2, _, (clpfd)).
:- module(rb2, _, [bf, trace]).

color(black).
color(red).

% :- iterative(red_black_tree/1, 2, (_(X,Y) :- Y is X + 1), 10).

red_black_tree(nil) <- .

red_black_tree(tree(Color, Left, Right)) <-
  trace,
  color(Color),
  subcolor(Color, LeftColor),
  subcolor(Color, RightColor),
  black_height(Left, H),
  black_height(Right, H),
  get_color(Left, LeftColor),
  get_color(Right, RightColor),
  red_black_tree(Left),
  red_black_tree(Right).

get_color(nil, black).
get_color(tree(C, _, _), C) :- color(C).

subcolor(black, C) :- color(C).
subcolor(red, black).

black_height(nil, 1).

black_height(tree(black, Left, Right), H) :-
  black_height(Left, LH),
  black_height(Right, RH),
  (LH > RH ->
    H is LH + 1
    ;
    H is RH + 1).

black_height(tree(red, Left, Right), H) :-
  black_height(Left, LH),
  black_height(Right, RH),
  (LH > RH ->
    H is LH
    ;
    H is RH).

% color_increment(black, 1) <- .
% color_increment(red, 0) <- .

