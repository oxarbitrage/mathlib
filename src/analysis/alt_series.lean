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
* `alternating_partial_sum'`: An alternating series whose first term is negative.

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
  (k : ℕ) :
  0 ≤ alternating_partial_sum a k :=
begin
  unfold alternating_partial_sum,
  induction k using nat.case_strong_induction_on with k hk,
  { simp only [sum_empty, range_zero] },
  { obtain heven | hodd := even_or_odd k,
    { simp only [sum_range_succ, neg_one_pow_of_even heven, one_mul, ge_iff_le],
      exact add_nonneg (hk k rfl.le) (ha_nonneg k), },
    { cases k with k,
      { exfalso, rw odd_iff_not_even at hodd, exact hodd even_zero, },
      { have : even k := by simpa with parity_simps using hodd,
        simp only [sum_range_succ, neg_one_pow_of_even this, neg_one_pow_of_odd hodd],
        rw [one_mul, neg_one_mul, add_assoc],
        apply add_nonneg (hk k (lt_succ_self k).le),
        rw [le_add_neg_iff_add_le, zero_add],
        exact ha_anti (lt_add_one k).le, } } },
end

lemma antitone.nat_suffix {m : ℕ}
  (ha_anti : antitone a) :
  antitone (λ (n : ℕ), a (m + n)) :=
λ x y hx, ha_anti (add_le_add_left hx m)

lemma alternating_partial_sum_even_mono
  {m n : ℕ}
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (hmn : m ≤ n)
  (hm : even m) :
  alternating_partial_sum a m ≤ alternating_partial_sum a n :=
begin
  unfold alternating_partial_sum,
  rw [← sub_nonneg],
  simp only [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range, even.neg_one_pow_add_left hm],
  apply alternating_partial_sum_nonneg _ (antitone.nat_suffix _ ha_anti),
  exact λ x, ha_nonneg (m + x),
end

lemma alternating_partial_sum_le_first
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (k : ℕ) :
  alternating_partial_sum a k ≤ a 0 :=
begin
  unfold alternating_partial_sum,
  induction k using nat.case_strong_induction_on with k hk,
  { simp only [sum_empty, range_zero, ha_nonneg 0] },
  { rw sum_range_succ,
    obtain heven | hodd := even_or_odd k,
    { rw [neg_one_pow_of_even heven, one_mul],
      cases k with k,
      { simp only [sum_empty, range_zero, zero_add] },
      { have : odd k := by simpa with parity_simps using heven,
        rw [sum_range_succ, neg_one_pow_of_odd this, neg_one_mul, add_assoc, add_comm],
        apply add_le_of_nonpos_of_le _ (hk k (le_succ k)),
        simp only [add_zero, neg_add_le_iff_le_add],
        exact ha_anti (lt_add_one k).le, } },
    { rw [neg_one_pow_of_odd hodd, neg_one_mul, add_neg_le_iff_le_add'],
      apply le_trans (hk k rfl.ge),
      exact le_add_of_nonneg_left (ha_nonneg k), } },
end

lemma alternating_partial_sum_diff_le_first
  {m n : ℕ}
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  (hmn : m ≤ n)
  (hm : even m) :
  alternating_partial_sum a n - alternating_partial_sum a m ≤ a m :=
begin
  unfold alternating_partial_sum,
  simp only [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range, even.neg_one_pow_add_left hm],
  apply alternating_partial_sum_le_first _ (antitone.nat_suffix a ha_anti),
  exact λ N, ha_nonneg (m + N),
end

-- Used to prove `cauchy_seq` for both `a n` and `-(a n)`
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma alternating_partial_sum_is_cau_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a) (ha_nonneg : ∀ (n : ℕ), 0 ≤ a n) (ε : ℝ) (hε : ε > 0) :
  ∃ N, ∀ n ≥ N, |alternating_partial_sum a n - alternating_partial_sum a N| < ε :=
begin
  -- Convert `tendsto` to `ε`-based definition of limit
  simp_rw [metric.tendsto_at_top, real.dist_0_eq_abs, abs_of_nonneg (ha_nonneg _)]
    at ha_tendsto_zero,
  obtain ⟨m, ha_tendsto_zero⟩ := ha_tendsto_zero ε hε,

  have : ∀ (m : ℕ) (hatz : ∀ (n : ℕ), n ≥ m → a n < ε) (hme : even m),
    ∀ (n : ℕ), n ≥ m → |alternating_partial_sum a n - alternating_partial_sum a m| < ε,
  { intros m hatz hme n hmn,
    have hps_mono := alternating_partial_sum_even_mono a ha_anti ha_nonneg hmn hme,
    rw abs_of_nonneg (sub_nonneg.mpr hps_mono),
    refine lt_of_le_of_lt _ (hatz m rfl.ge),
    exact alternating_partial_sum_diff_le_first a ha_anti ha_nonneg hmn hme },

  obtain hme | hmo := even_or_odd m,
  { exact ⟨m, this m ha_tendsto_zero hme⟩, },
  { use m+1,
    apply this,
    { intros n hn,
      exact ha_tendsto_zero _ (le_of_succ_le hn), },
    { simpa with parity_simps using hmo, } },
end

theorem alternating_partial_sum_is_cauchy_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n) :
  cauchy_seq (alternating_partial_sum a) :=
begin
  simp only [metric.cauchy_seq_iff', real.dist_eq],
  exact alternating_partial_sum_is_cau_seq a ha_tendsto_zero ha_anti ha_nonneg,
end

theorem alternating_partial_sum_is_cauchy_seq'
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n) :
  cauchy_seq (alternating_partial_sum' a) :=
begin
  simp only [metric.cauchy_seq_iff', alternating_partial_sum', real.dist_eq,
    neg_sub_neg, sum_neg_distrib, mul_neg_eq_neg_mul_symm],
  have hcs := alternating_partial_sum_is_cau_seq a ha_tendsto_zero ha_anti ha_nonneg,
  simpa only [abs_sub_comm] using hcs,
end
