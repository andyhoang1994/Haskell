# Haskell School Assignments

Assignments for Symbolic Computing class.

Mathematical program that uses symbolic data strutures for algebraic expressions in order to parse, un-parse, simplify, and calculate derivatives. It can alternate between regular math notation such as ```4 + x^2``` and symbolic expressions such as ```(Add (Mul (Num 4) (Power (Var 'x') 2))```. It uses an inside-out approach for expression simplification.

Regular expression searcher that uses the Glushkov NFA in order to efficiently search large texts for any regular expression. Regular expressions come in the form of ```b(a|b)*le``` and all strings that fit the regular expression will be returned. The program uses a bit-parallel method, using bit vectors as states in order to sequentially find strings that match the given regular expression.
