# Proof-mining-
Implementations of the applications of proof mining to areas of Mathematics, particularly non-linear analysis in Lean, with an eye on recursive inequalities and computable analysis.

We define basic concepts used in the proof mining literature, when studying convergence in non-linear analysis, such as rates of convergence and metastability. We focus on formalising computationally affective versions of results relating to sequences of real numbers satisfying recursive inequalities. The convergence of sequences satisfying such inequalities are used as lemmas in theorems relating to the convergence of many iterative algorithms found in the non-linear analysis literature, thus formalising computationally effective versions of these inequalities will allow one to easily formalise computationally effective versions of such algorithms. 

We also provide a construction of a sequence of computable rational numbers, which converge to zero but do not have a computable rate of convergence (modulo defining computable functions on the rational numbers). The sequence we chose is parameterised in terms of a non-decreasing sequence which means it can easily be adapted to construct other sequences of computable numbers without computable rates of convergences satisfying other properties of interest.

Future Work: 

Prove that the Rationals are pimcodable, thus finishing the construction of the sequence of rational numbers without a computable rate of convergence.

Add to the case studies of quantitative convergences theorems of sequences of numbers satisfying recursive inequalities.

Construct more examples of these so called 'Specker sequences' and implement more things in computable analysis.


