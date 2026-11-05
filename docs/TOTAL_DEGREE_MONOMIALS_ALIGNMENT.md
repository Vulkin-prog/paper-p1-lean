# Exact triangular monomial coordinates with degree and height control

Source: main13.4 and the bounded-coefficient preparation for its geometric plane specialization. Total degree is preserved exactly, including signed integer coordinates and degree zero.

TotalDegreeMonomials defines the actual triangular monomial index x+y<=D and its integer polynomial reconstruction. coefficient_formula proves the literal coefficient sum, coefficient recovers every indexed coordinate exactly, and coefficient_zero_of_total_lt proves all terms above D vanish. total_degree_le and reconstruction show these coordinates describe exactly the integer polynomials of total degree at most D, without replacing total degree by a rectangular partial-degree bound.

ne_zero proves nonzero coordinates give a nonzero polynomial, evaluation gives the exact finite monomial row identity at signed integer points, height_le transfers a uniform coefficient bound to the actual polynomial height, and index_card_pos supplies the nonempty finite coefficient dimension including D=0.

These are the algebraic prerequisites for constructing a bounded-height equation through an actual grid population using the already proved finite integer kernel theorem. The bounded-height construction and its counting reduction remain to be assembled; no grid count is assumed or proved by this module.

P1-MATH-0367 adds nine theorems and two index/polynomial definitions. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records365 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 and the geometric integer plane count remain open; Palomar remains deferred.
