# Examples

Some examples of transformations we want, written in Haskell-like pseudocode.

## Numeric intervals

### Simple filter

filter (< 5) (choose (1, 10)) ===>  choose (1, 4)

### Interval intersection

    filter (And (> 2) (< 7)) (choose (1, 10))  ===>  intersect (choose (3, 10)) (choose (1, 6))
                                                    = choose (3, 6)

### Interval union

    filter (Or (< 3) (And (> 4) (< 9))) (choose (1, 10))  ===>  union (choose (1, 2)) (choose (5, 8))

The general situation here is sort of like the "usual" topology on the real numbers: an open set is a union of basic opens (intervals).

Are topological ideas useful here?

## Other numeric predicates

    filter ((< 1) . (`mod` 2)) (choose (1, 10))  ===>  map (*2) (choose (1, 5))

