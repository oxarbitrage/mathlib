/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/

import analysis.normed_space.basic

/-!
# Convergence of alternating series

An alternating series is an infinite series of the form
$\sum_{k=0}^{\infty} (-1)^k a_k$ or $\sum_{k=0}^{\infty} (-1)^{k+1} a_k$,
where $a_n : \real$ and $a_n \ge 0$.

The **alternating series test** states that an alternating series is convergent if
$\lim_{n\to\infty} a_n = 0$ and $a_{n+1} \leq a_n$. We prove this via the Cauchy
convergence test by showing that its partial sums, $s_k = \sum_0^k (-1)^k a_k$,
form a Cauchy sequence.

Even though they are Cauchy, alternating series do not fulfill the current
definition of `summable` in mathlib, which requires that a series be
*absolutely* convergent.  Alternating series are only *conditionally*
convergent.

## Main definitions

* `alternating_partial_sum` : An alternating series whose first term is positive.
* `alternating_partial_sum'`: An alternating series whose first term is positive.

## Main results

* `alternating_partial_sum_is_cauchy_seq`: The partial sums of an alternating series
  form a Cauchy sequence.
* `alternating_partial_sum_is_cauchy_seq'`: Same as above, but for series whose first
  term is negative.

## References

* https://en.wikipedia.org/wiki/Alternating_series

## Tags

series, alternating series, Cauchy convergence test
-/

open nat filter finset
open_locale big_operators topological_space

variable a : ℕ → ℝ

/-- The partial sum of an alternating series whose first term is positive -/
def alternating_partial_sum (k : ℕ) := ∑ n in range k, (-1)^n * a n

/-- The partial sum of an alternating series whose first term is negative -/
def alternating_partial_sum' (k : ℕ) := ∑ n in range k, (-1)^n * -(a n)

lemma alternating_partial_sum_nonneg
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (k : ℕ)
  : 0 ≤ alternating_partial_sum a k :=
begin
  unfold alternating_partial_sum,
  induction k using nat.case_strong_induction_on with k hk,
    { simp only [sum_empty, ge_iff_le, range_zero] },

  rw sum_range_succ,
  obtain even | odd := even_or_odd k,
  { rw neg_one_pow_of_even even,
    simp only [one_mul, ge_iff_le],

    refine add_nonneg _ _,
    exact hk k (le_refl k),
    exact ha_nonneg k},

  cases k with k,
  { simp, exact ha_nonneg 0 },

  rw sum_range_succ,
  rw [neg_one_pow_of_even _, neg_one_pow_of_odd odd], swap,
  { rwa [odd_iff_not_even, even_succ, not_not] at odd },
  rw [one_mul, neg_one_mul, add_assoc],

  refine add_nonneg _ _,
  { exact hk k (le_of_lt (lt_succ_self k)) },
  simp only [zero_add, le_add_neg_iff_add_le],
  exact ha_anti (le_of_lt (lt_add_one k)),
end

lemma anti_suffix_is_anti {m : ℕ}
  (ha_anti : antitone a) :
  antitone (λ (n : ℕ), a (m + n)) :=
begin
  intros x y hx,
  apply ha_anti,
  linarith,
end

lemma alternating_partial_sum_diff_nonneg
  {m n : ℕ}
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (hmn : m ≤ n)
  (hm : even m)
  : 0 ≤ alternating_partial_sum a n - alternating_partial_sum a m :=
begin
  unfold alternating_partial_sum,
  rw [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range],
  simp only [neg_one_pow_of_even_add hm],
  apply alternating_partial_sum_nonneg,
  { exact anti_suffix_is_anti _ ha_anti },
  { intro x, exact ha_nonneg (m + x) },
end

lemma alternating_partial_sum_le_first
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (k: ℕ)
  : alternating_partial_sum a k ≤ a 0 :=
begin
  unfold alternating_partial_sum,

  induction k using nat.case_strong_induction_on with k hk,
  { simp only [sum_empty, range_zero], exact ha_nonneg 0 },

  rw sum_range_succ,
  obtain even | odd := even_or_odd k, swap,
  { rw [neg_one_pow_of_odd odd, neg_one_mul],
    specialize hk k rfl.ge,
    rw add_neg_le_iff_le_add',

    apply le_trans hk (_: a 0 ≤ a k + a 0),
    rw [le_add_iff_nonneg_left],
    exact ha_nonneg k },

  rw [neg_one_pow_of_even even, one_mul],

  cases k with k,
  { simp only [sum_empty, range_zero, zero_add] },

  rw sum_range_succ,
  rw neg_one_pow_of_odd, swap,
  { rwa [even_succ, even_iff_not_odd, not_not] at even },
  rw [neg_one_mul, add_assoc, add_comm],
  specialize hk k (le_succ k),
  apply add_le_of_nonpos_of_le _ hk,
  simp only [add_zero, neg_add_le_iff_le_add],
  exact ha_anti (le_of_lt (lt_add_one k)),
end

lemma alternating_partial_sum_diff_le_first
  {m n : ℕ}
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (hmn : m ≤ n)
  (hm : even m)
  : alternating_partial_sum a n - alternating_partial_sum a m ≤ a m :=
begin
  unfold alternating_partial_sum,
  rw [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range],
  simp only [neg_one_pow_of_even_add hm],

  apply alternating_partial_sum_le_first _ (anti_suffix_is_anti a ha_anti),
  dsimp,
  intro N,
  exact ha_nonneg (m + N),
end

-- Used to prove `cauchy_seq` for both `a n` and `-(a n)`
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma alternating_partial_sum_is_cau_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ (n : ℕ), 0 ≤ a n) :
  ∀ (ε : ℝ),
    ε > 0 →
    (∃ (N : ℕ),
       ∀ (n : ℕ),
         n ≥ N → |alternating_partial_sum a n - alternating_partial_sum a N| < ε) :=
begin
  intros ε hε,

  -- Convert `tendsto` to `ε`-based definition of limit
  simp_rw [metric.tendsto_at_top, real.dist_0_eq_abs, abs_of_nonneg (ha_nonneg _)]
    at ha_tendsto_zero,
  specialize ha_tendsto_zero ε hε,
  cases ha_tendsto_zero with m ha_tendsto_zero,

  obtain hme | hmo := even_or_odd m,
  { use m,
    intros n hmn,

    have diff_nonneg := alternating_partial_sum_diff_nonneg a ha_anti ha_nonneg hmn hme,
    have diff_le_first := alternating_partial_sum_diff_le_first a ha_anti ha_nonneg hmn hme,

    rw [abs_of_nonneg diff_nonneg],
    apply lt_of_le_of_lt diff_le_first _,
    exact ha_tendsto_zero m rfl.ge },
  { use (m+1),
    have hm1e : even (m+1) := even_succ.mpr (odd_iff_not_even.mp hmo),
    intros n hmn,

    have diff_nonneg := alternating_partial_sum_diff_nonneg a ha_anti ha_nonneg hmn hm1e,
    have diff_le_first := alternating_partial_sum_diff_le_first a ha_anti ha_nonneg hmn hm1e,

    rw [abs_of_nonneg diff_nonneg],
    apply lt_of_le_of_lt diff_le_first _,
    apply ha_tendsto_zero,
    exact le_succ m },
end

theorem alternating_partial_sum_is_cauchy_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : cauchy_seq (alternating_partial_sum a) :=
begin
  apply metric.cauchy_seq_iff'.mpr, swap,
  { exact has_bot_nonempty ℕ },

  simp only [real.dist_eq],
  exact alternating_partial_sum_is_cau_seq a ha_tendsto_zero ha_anti ha_nonneg,
end

theorem alternating_partial_sum_is_cauchy_seq'
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : cauchy_seq (alternating_partial_sum' a) :=
begin
  apply metric.cauchy_seq_iff'.mpr, swap,
  { exact has_bot_nonempty ℕ },

  unfold alternating_partial_sum',
  simp only [real.dist_eq, neg_sub_neg, sum_neg_distrib, mul_neg_eq_neg_mul_symm],

  -- For some reason, `simp_rw [abs_sub_comm]` only works on a hypothesis, not the goal
  have hcs := alternating_partial_sum_is_cau_seq,
  unfold alternating_partial_sum at hcs,
  simp_rw [abs_sub_comm] at hcs,
  exact hcs a ha_tendsto_zero ha_anti ha_nonneg,
end
