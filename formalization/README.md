# Lean formalization of *General Constructions of Permutation-Fair Dice*

The project contains Lean 4 proofs of the current article's construction
and bound conclusions, including the prescribed quadratic individual-die
upper bound and the random-palindrome approximation theorem. The scope includes
`sections/individual-dice.tex` and `sections/approximate-fairness*.tex`;
research notes in `research/` are excluded. Classical mathematical inputs
are explicit theorem parameters, not new Lean axioms: results that use
these inputs are conditional on the premises listed below.

## Check the proofs

The toolchain is Lean **4.32.1**, with mathlib **v4.32.1** pinned by
`lake-manifest.json` (mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`). With Elan installed, run:

```sh
cd formalization
lake exe cache get
./check.sh
```

Run Lake from this directory so that it selects this project's toolchain.
`check.sh` builds the aggregate module [FairDice.lean](FairDice.lean), then
runs [Audit.lean](Audit.lean). The audit traverses **every declaration in the
`FairDice` namespace**, checking all transitive axiom dependencies. It fails
on anything outside `propext`, `Classical.choice`, and `Quot.sound`, including
`sorryAx`, custom axioms, or native evaluation axioms. The finite examples use
kernel-checked `decide`.

## Mathematical model

* A word is a `List α`. `count p s` counts position subsequences, and
  `count_eq_sublists` proves agreement with Lean's enumeration of sublists.
  Repeated equal subsequences are counted separately.
* `PermutationFair` includes the presence of every die and equal counts for
  all full permutations. `patternProbability` divides the pattern count by
  the product of the relevant face counts. Its normalization and its
  equivalence with uniform permutation probabilities are proved.
* The constructions produce actual finite words. Restriction, relabeling,
  blowup, repetition, and gap insertion operate on those words, with their
  counting identities proved from the subsequence definition.
* Hahn polynomials, their norms, their integrals, and the projection weights
  are concrete rational expressions. The rational polynomial integral is
  proved equal to the usual real interval integral. Positivity, common
  denominators, integer gaps, and size bounds are derived, not assumed.
* Full-set go-first fairness uses counts of winning outcomes. Place-fair
  constructions use `RankedDice`: distinct integer face labels and rank
  generating polynomials. `rankGenerating_coeff` identifies coefficients
  with literal finite outcome counts. `WordPlaceFair` supplies the word
  version, including unequal multiplicities, for hereditary lower bounds.
* The random-construction calculation uses an actual product of uniform
  Lebesgue measures on `[0,1]`, with a measurable sum of order indicators.

The earlier linear individual-die bound uses monomial moments and a
Hilbert matrix. The new quadratic bound uses the article's monotone mixed
moments and paired Gaussian/Radau tests. Both apply to actual fair words,
including unequal face counts. Asymptotic theorems use explicit constants
or the corresponding eventual quantifiers.

## Current article: verified coverage

The lower bound `each_die_quadratic` proves
`((card α : ℝ) - 1)^2 / 200 ≤ s.count a` for every die of an actual
permutation-fair word when `card α ≥ 2`. The only input is
`ClassicalQuadratureExternal`, containing classical univariate quadrature
properties. The monotone comparison model, its mixed moments, the paired
tests, the last-row inequality, and the deduction for dice are proved.

The converse is `prescribed_individual_size`: for every `n >= 2`, every
`K >= C*n^2`, and any specified die, it constructs an actual finite fair
word with exactly `K` copies of that die and equal positive multiplicities
for the others. Its only input is `GilboaPeledExternal`. The intermediate
order law, rational-grid realization and integer face counts are proved.
`optimal_individual_size` defines the genuine minimum and proves the
two-sided bounds `n^2/800 <= g(n) <= C*n^2`.

| Current TeX statement | Verified declarations / status |
| --- | --- |
| `individual-paired-thresholds` | `paired_thresholds`, including zero rows and all endpoint cases |
| `individual-diagonal-identity` | `MonotoneMoments.shifted_identity`, `injective_shifted_identity`, `extra_coordinate_identity`; `comparisonModel` derives the required moments from a fair word |
| `individual-quadrature-facts` | Classical Gaussian/Radau data are explicit inputs; `GaussianData.edge_bound` derives the Gaussian endpoint estimate from Jacobi comparison |
| `individual-last-row` | `last_row_gaussian`, `last_row_endpoint_lower`, `paired_last_ratio`, `last_row_weight_bound`, with the constant 200 |
| `thm:individual-size`, lower bound | `each_die_quadratic` |
| Starting-rule support and pivots | `real_rule_support_card`, `real_rule_pivots`, `momentJacobian_isUnit`, `matching_pivot_collision_derivative`, `moment_perturbation_exists`, `regular_moment_perturbation`, `regular_starting_quadrature`: actual analytic implicit map, collision separation, inward endpoint motion and exact regularization at every admissible cardinality |
| `individual-centered-bumps` | `centered_bump_exists`, `CorrectionIntervals.left_moments`, `right_moments`, `full_moments`, `bump_rational`, `locally_bounded`; literal piecewise constant functions, rational breakpoints, continuous coefficients, support and uniform bounds |
| Polynomial multi-bump cancellation | `tensor_polynomial_cancellation`, `multi_bump_polynomial_zero`; `correctionPrimitive_support`, `correctionIterate_support_moments`, `densityPrefix_expansion`: compact support persists under the required integrations, and every nonlinear interaction in the actual ordered-prefix integral vanishes |
| One-bump order-response kernels | `predecessor_bump_response`, `successor_bump_response`: actual integrals against the centered steps; all non-neighbor contributions vanish |
| `individual-correction-system` | `rational_vandermonde_correction`, `derivative_moment_correction`, `corrected_rank_probability` |
| Positive rational approximation and densities | `positive_rational_density_approximation`, `densityCoefficients_moments`, `densityCoefficients_rational`, `correctedDensity_integral`, `correctedDensity_rational`: actual inverse-formula coefficients, simultaneous positivity at least `1/2`, mass one, rational values |
| Common correction functional | `densityMomentFunctional_eq`, `densityMomentFunctional_derivative`: every selected node set gives the same functional and repairs every polynomial through degree `m` |
| Complete corrected-density family from a regular rule | `corrected_family_exists`: constructs distinct rational interior nodes, disjoint index selections and supports, positive normalized rational-valued densities, and all repaired moments; `prescribed_density_family` supplies the regular rule and this entire family from the classical Gilboa–Peled threshold |
| `individual-order-response` and `individual-response-formula` | `densityPrefix_at_node`, `CorrectedFamily.order_response`, `CorrectedFamily.uniform_order`: only the immediate neighbors survive, their response is the derivative of `orderKernel`, and the repaired moments give every full order exactly `1/(m+1)!` |
| Integer realization of cell profiles | `rational_cell_masses_integer`, `finite_cell_profiles`, `fair_cell_probability`, `patternProbability_blocks`: one common denominator, literal fair blowup blocks with equal total face counts, and the normalized cut expansion |
| Continuous-to-finite realization | `CorrectedFamily.grid_model`, `densityPrefixFrom_split`, `densityPrefixFrom_constant`, `grid_blocks_prefix_suffix`, `markedCount_insertCellGaps`, `CorrectedFamily.finite_realization`: all breakpoints and nodes share a rational grid; literal prefix and suffix counts equal the iterated integrals; insertion preserves exactly `K` distinguished faces |
| `thm:individual-size`, upper bound | `individual_faces_upper`, `prescribed_individual_size`: every sufficiently large prescribed `K`, any chosen die, equal finite sizes for all other dice |
| Introduction: `g(n)=Theta(n^2)` | `smallestDieFaces_attainable`, `smallestDieFaces_le`, `optimal_individual_size`: an attained minimum and explicit uniform bounds |
| `eq:random-palindrome-word` | `palindromeWord`, `palindromeWord_multiplicity` (exactly `2*m` faces per die) |
| Pairwise fairness and `eq:palindrome-delta-bound` | `palindrome_pair_count`, `palindromeDelta_short`, `count_palindrome_le_two`, `palindromeDelta_bound` |
| Actual homogeneous block expansion | `palindrome_block_part_expansion`, `palindrome_error_nonempty_parts`, `palindrome_part_depends`, `palindrome_part_centered`: exact nonempty-block decomposition and separate centering of each selected part |
| Independence of disjoint segments | `disjoint_relative_orders_uniform`, `disjoint_block_orders_uniform`, `disjoint_segment_errors_uniform`: the actual uniform global permutations induce the product of uniform relative-order laws on disjoint alphabets, including independent blocks |
| Fixed-length residue classes | `residue_segment_alphabets_disjoint`: consecutive segments of one length and one residue class have disjoint actual alphabets for every target permutation |
| Centering under uniform relabelling | `relabel_two_count_mean`, `palindromeDelta_centered`, `palindrome_relative_error_mean`; the entire actual word has normalized mean one |
| `eq:palindrome-expansion` | `count_blocks`, `palindrome_occupancy_expansion`, `palindrome_occupancy_weights_sum`: exact cut expansion for the concrete word and normalization of its multinomial weights |
| Multinomial/Poisson calculation | `multinomialMass_sum`, `multinomialCollision_le_one`, `poisson_multinomial_identity`, `poisson_collision_bound` |
| `lem:palindrome-lattice` | `palindrome_lattice_bound`, conditional on the two scalar estimates in `PoissonEstimates`; the composition summation and constants are derived |
| Selected-gap occupancy coefficients | `gap_reciprocal_factorials`, `selected_gap_mass_formula`, `grouped_multinomial_marginal`, `palindrome_selected_gap_coefficient`, `palindrome_selected_gap_formula`: sum over every unselected occupancy in each literal block gap and derive `eq:palindrome-coefficient` for the actual cut coefficients, including zero gaps and zero remaining-letter counts |
| Squared selected-gap coefficients | `selected_gap_squared_sum`, `selected_lattice_squared_bound`, `short_lattice_constant`: their exact squared sum is the multinomial collision probability times the scalar prefactor; the lattice bound and the short-support constant 160 follow |
| Actual squared cut coefficients | `gap_coefficient_energy`, `actual_gap_colored_squared_sum`: the inverse-retention energy of the actual segment coefficients agrees with the selected-gap formula, and its sum over all gap letter counts is exactly the multinomial collision probability times the scalar prefactor |
| Actual block selections and the lattice bound | `blockSelectionGapEmbedding`, `actual_block_collision_lattice`, `actual_selected_lattice_energy`, `actual_short_length_energy`: literal selected block sets have distinct gap vectors; summing their actual coefficients over all block sets and all segment starts gives the lattice bound and the short-support constant 160 for every fixed length vector |
| Short- and long-support series | `palindrome_length_series_bound`, `palindrome_block_series_bound`, `factorial_sqrt_series_bound` |
| `lem:palindrome-chaos` for finite product spaces | `bounded_independent_chaos`: independent-copy symmetrization, Jensen, coordinate swaps, and the energy bound; conditional only on classical Rademacher Bonami hypercontractivity |
| Chaos of actual disjoint segments | `disjoint_segment_chaos`: transports the norm through the proved relative-order law and applies the chaos bound to actual palindrome segment errors; only Bonami is an external premise |
| Coloring averages and energy | `coloredSum_mean`, `coloredEnergy_mean`, `colored_average_bound`: retention rescales the mean correctly and contributes one inverse retention probability to the squared energy; the norm estimate for each fixed color is an explicit hypothesis |
| Actual size/residue colors and `eq:palindrome-colored` | `colorRetains_mean`, `segment_term_retention_mean`, `fixed_color_segment_chaos`, `palindrome_colored`: literal finite random colors, their product retention probability, disjoint retained alphabets, and the complete norm bound; only classical Bonami is external |
| Coloring the concrete cut expansion | `cutSegment_pattern`, `cutGraph_error_product`, `cut_product_eq_zero_of_short`, `palindrome_segment_part_expansion`: identify every contributing cut part with its actual consecutive segment and group all cut multiplicities into nonnegative `palindromeSegmentCoefficient`; its degree and one-segment-per-block support are proved |
| Norm of the actual word error | `palindrome_homogeneous_colored`, `palindrome_error_by_degree`, `palindrome_error_colored_bound`: apply the coloring theorem to the actual coefficients and sum the homogeneous parts; no coefficient or independence hypothesis is supplied |
| Concrete coefficients as multinomial marginals | `patternCuts_nodup`, `cutOccupancyEquiv`, `palindromeCutWeight_occupancy`, `palindromeSegmentCoefficient_multinomial`: the concrete cuts and weak compositions are bijective, their weights agree, and each actual segment coefficient is the multinomial probability of its derived selection event |
| Complete support and length summation | `palindrome_coefficient_parameter`, `palindrome_restricted_energy`, `palindrome_short_energy`, `palindrome_global_energy`, `palindrome_long_energy`: every nonzero actual monomial is covered by admissible lengths, actual block sets and gap counts; the complete short-support, global and exponentially tilted energies are bounded |
| `lem:palindrome-moment` | `palindrome_short_long_norm`, `palindrome_global_norm`, `palindrome_uniform_moment`: complete norm estimates for the actual word, including all small `n`, the threshold `8*n^(11/10)*p^(1/5)` and final constant 32; only Bonami and the two scalar Poisson estimates are external |
| Markov and union step for the concrete word | `palindrome_good_probability_of_chosen_moments`: the asserted moment margin implies simultaneous success with probability at least `1/2` and existence of a suitable word; only the moment margin remains an explicit hypothesis |
| Random-palindrome `thm:approximate` | `palindrome_approximate`: explicit constant 16, exact exponents `13/10`, `1/5`, `-2/5`, and the final probability conclusion; the moment estimate is supplied by its proved theorem |
| Choice of moment order | `palindromeMomentOrder_lower`, `palindromeMomentOrder_upper`, `palindromeMomentOrder_log_bound`, `palindromeMomentOrder_tail`: the actual `max(2, log(2*n!)/log 3)` lies in `[2,n^2]`, is at most `2*n*log n`, and pays for the factorial union bound |

The individual-die upper bound and the random-palindrome moment and
approximation theorems are proved. The explicit classical inputs remain
premises; no article-specific construction, response law, coefficient
estimate or final dice conclusion is assumed as an external input.

The aggregate build imports every module in the extension, and the axiom
audit checks all of their declarations. The older theorem
`approximate_permutation_fairness` is about periodic words and **does not
prove the new random-palindrome theorem**.

## Earlier manuscript correspondence

This table describes the earlier manuscript. Some labels and statements
have since been replaced; consult the current-section table above for the
new individual-die and random-palindrome results. All declarations are in
the `FairDice` namespace.

| Paper statement | Lean declarations | File |
| --- | --- | --- |
| `lem:dice-string` | `count_eq_sublists`, `permutationFair_iff_uniform` | [Basic](FairDice/Basic.lean), [Probability](FairDice/Probability.lean) |
| `clm:restriction-blowup` | `permutationFair_restrict`, `permutationFair_blowup` | [Restriction](FairDice/Restriction.lean), [Blowup](FairDice/Blowup.lean) |
| `cor:equalize` | `equalize` | [Equalization](FairDice/Equalization.lean) |
| `lem:partial` | `partial_count_product`, `permutationFair_partialOrder` | [PartialPatterns](FairDice/PartialPatterns.lean) |
| `cor:self-concat` | `permutationFair_repeat` | [Powers](FairDice/Powers.lean) |
| `lem:equal-full-to-partial` | `equal_full_to_partial` | [PartialPatterns](FairDice/PartialPatterns.lean) |
| `lem:symmetrize` | `fairUpTo_symmetrize`, `length_symmetrize` | [Symmetrization](FairDice/Symmetrization.lean) |
| `thm:first-size` | `elementary_construction`, `elementary_faces_exponential` | [Elementary](FairDice/Elementary.lean), [MainResults](FairDice/MainResults.lean) |
| `lem:insertion` | `insertion_fair_of_moments`, `markedCount_insertGaps` | [InsertionFairness](FairDice/InsertionFairness.lean), [Insertion](FairDice/Insertion.lean) |
| `prop:quadrature` | `hahnWeight_exact`, `hahnWeight_pos` | [Hahn](FairDice/Hahn.lean), [HahnPositivity](FairDice/HahnPositivity.lean) |
| `thm:main` | `hahn_construction`, `hahn_construction_exponential` | [HahnConstruction](FairDice/HahnConstruction.lean), [MainResults](FairDice/MainResults.lean) |
| `thm:many-large` | `many_large_exponential` | [ManyLarge](FairDice/ManyLarge.lean) |
| `lem:exp-lower` | `exponential_length_lower` | [ExponentialLowerBound](FairDice/ExponentialLowerBound.lean) |
| Earlier `thm:each-die-linear` | `each_die_linear` | [IndividualLower](FairDice/IndividualLower.lean) |
| `prop:rational-design-insertion` | `rational_design_insertion_on_grid`, `rational_design_insertion` | [RationalDesigns](FairDice/RationalDesigns.lean) |
| `cor:rational-design-q3` | `rational_design_counterexamples`, `rational_design_sequence_counterexample` | [DesignCounterexamples](FairDice/DesignCounterexamples.lean) |
| `thm:go-first-optimum` | `goFirst_optimum`, `staircase_construction`, `goFirst_length_lower` | [MainResults](FairDice/MainResults.lean), [Staircase](FairDice/Staircase.lean), [GoFirstLower](FairDice/GoFirstLower.lean) |
| `thm:place-moment` | `moment_coloring_construction` | [PlaceConstruction](FairDice/PlaceConstruction.lean) |
| `thm:place-prouhet` | `improved_place_construction`, `prouhet_place_construction` | [Multigrade](FairDice/Multigrade.lean) |
| Earlier periodic approximation theorem | `approximate_permutation_fairness`, `approximate_l1`, `approximate_total_variation` | [Approximation](FairDice/Approximation.lean) |

The informal existence and size theorems in the introduction are covered by
`elementary_construction`, `hahn_construction_exponential`, and
`exists_exponentially_large_die`.

## Additional calculations and remarks

| Calculation | Lean declarations |
| --- | --- |
| Unequal three-die example: counts `(4,6,2)`, eight of every order | `unequalThree_multiplicities`, `unequalThree_counts`, `unequalThree_fair` |
| Simpson-rule example: twelve faces per die, 288 of every order | `simpsonThree_multiplicities`, `simpsonThree_counts`, `simpsonThree_fair` |
| Failure of correction at only three nodes | `left_grid_first_moment`, `left_grid_second_moment`, `three_node_correction_weight`, `three_node_correction_negative` |
| Hahn denominator clearing and exponential size | `hahnWeight_denominator`, `commonDenominator_bound`, `hahnFaces_exponential_bound` |
| Divisibility conditions admit `(1,n!,...,n!)` | `factorial_constraints_allow_one` |
| Hahn rule as a rational equal-weight design | `RationalRule.equal_weight_design`, `hahn_equal_weight_design` |
| Hereditary go-first prime product and exponential large die | `hereditary_prime_product`, `hereditary_exponentially_large_die` |
| Same conclusions for hereditary place fairness | `hereditaryPlace_prime_product`, `hereditaryPlace_exponentially_large_die` |
| Equal multiplicities force `rad(n!) ∣ m` | `hereditary_equal_primorial_dvd`, `hereditaryPlace_equal_primorial_dvd` (`primorial n` is the product of primes at most `n`) |
| Translation of Choudhry's partition by minus one | `translate_moments` |
| Mean, single-face sensitivity, overlap, concentration and union bound for random labels | `randomPatternCount_expectation`, `randomPatternCount_bounded_difference`, `outcome_overlap_bound`, `randomPatternCount_tail`, `random_all_patterns_tail` |
| Collision estimate for total variation | `periodic_total_variation_collision`, `periodic_total_variation_quadratic` |
| Necessary periodic face count, including the explicit bound `n²/(8ε)` | `periodic_faces_necessary`, `periodic_faces_quadratic_necessary` |
| Approximate first-place lower bound, `eq:approx-first-lower` | `approximate_first_occurrence_bound`, `approximate_first_ranks` |
| Quadratic total length from approximate marginals or pointwise approximation | `approximate_goFirst_quadratic`, `pointwise_implies_first_marginal`, `pointwise_approximation_length_lower` |

## External premises

These are **conditional proofs** wherever an external premise occurs. The
kernel audit checks that no premise is hidden as an axiom; it does not supply
proofs of the premises themselves.

| Parameter | Precisely what is assumed | Where used |
| --- | --- | --- |
| `HahnExternal` | Classical Hahn orthogonality, norm formula, spanning property, Zaremba's nodal bound (`lem:Q-supnorm`), and Wilson's odd/even integral estimates (`lem:wilson-integral`) | Hahn quadrature, integer construction and rational-design upper bound |
| `PrimorialExternal` | A positive exponential lower bound on the primorial for sufficiently large integers | Exponential lower bounds |
| `ProuhetExternal` | Classical digit-sum moment identity (`lem:prouhet`) | Prouhet place-fair construction |
| `ChoudhryExternal` | Consecutive partition of `1,...,2*n^(n-2)` into classes with equal moments through degree `n-2`, including equal sizes | Improved place-fair construction |
| `PPartitionExternal` | Stanley's classical descent enumeration specialized to the periodic word | Pointwise approximation and periodic collision/necessary-size bounds |
| `ContinuousOrderExternal` | An injectively selected list of independent continuous uniform coordinates has any prescribed strict order with probability `1/n!` | Random-label expectation |
| `BoundedDifferencesExternal` | The general McDiarmid inequality for a measurable function on a product space with specified coordinate sensitivities | Earlier random-label concentration |
| `ClassicalQuadratureExternal` | Positive exact Gaussian and right-Radau rules on `[0,1]`, their ordered interior nodes, Gaussian Jacobi cosine comparison, Radau endpoint weight and reciprocal root sum | New quadratic individual-die lower bound |
| `PoissonEstimates` | For nonnegative rate, every Poisson mass is at most `2/sqrt(1+rate)`; the mass at integer mean `d` is at least `1/(3*sqrt(d+1))` | New lattice collision bound; these scalar classical estimates have not been derived from Stirling inside this project |
| `GilboaPeledExternal` | Equal-weight quadrature for the constant weight at every cardinality `K >= C*d^2`, allowing repeated and endpoint nodes ([Theorem 1.1](https://arxiv.org/pdf/1507.01505)); distinctness and interior regularization are proved locally | Prescribed-size density family and finite individual-die upper bound |
| `BonamiExternal` | The degree-`ell` Rademacher hypercontractive inequality, stated as a finite uniform `p`-moment estimate for a homogeneous multilinear polynomial, `p >= 2` | Bounded independent chaos; centering, symmetrization, Jensen and the general-variable bound are proved in Lean |

The elementary construction, restriction and blowup identities,
equalization, individual linear lower bound, rational-design insertion,
go-first optimum, moment-coloring reduction, and approximate-marginal lower
bounds require none of these external premises.

The earlier conjecture is retained as `EveryDieExponential`, together with
the earlier conditional rational-design counterexamples. It is historical
material, not an assertion that the current manuscript leaves that problem
open. Historical priority, attribution, bibliographic comparisons, and
other authors' shuffle-cutoff results are not assertions of new Lean proofs
in this project.
The correspondence table describes verified theorem statements, not a
line-by-line encoding of the surrounding prose.
