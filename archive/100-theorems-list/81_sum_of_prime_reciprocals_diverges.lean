/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import topology.instances.ennreal
import algebra.squarefree

/-!
# Divergence of the Prime Reciprocal Series
This file proves Theorem 81 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).
The theorem states that the sum of the reciprocals of all prime numbers diverges.
The formalization follows Erdős's proof by upper and lower estimates.

## References
https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes
-/

open_locale big_operators
open_locale classical
open filter finset

lemma card_le_div_nat {n p : ℕ} (hp : 0 < p) : card {e ∈ range n | p ∣ (e + 1)} ≤ n / p :=
begin
  let f : ℕ → ℕ := λ e, (e + 1) / p - 1,
  let Np := {e ∈ range n | p ∣ (e + 1)},

  have hf : ∀ a : ℕ, a ∈ Np → f a ∈ range (n / p),
  { intros a ha,
    simp only [Np, sep_def, mem_filter, mem_range] at ha,
    obtain ⟨han, ⟨w, hw⟩⟩ := ha,
    simp only [f, mem_range],
    have hnp : n / p ≥ 1,
    { rw ← nat.div_self hp,
      exact nat.div_le_div_right (show n ≥ p, by nlinarith [(show w > 0, by nlinarith)]) },
    calc (a + 1) / p - 1 ≤ n / p - 1 : nat.sub_le_sub_right
                                         (nat.div_le_div_right (nat.succ_le_iff.mpr han)) 1
    ...                  < n / p     : nat.sub_lt (by linarith) zero_lt_one },

  have hf_inj : ∀ (a₁ : ℕ), a₁ ∈ Np → ∀ (a₂ : ℕ), a₂ ∈ Np → f a₁ = f a₂ → a₁ = a₂,
  { intros a₁ ha₁ a₂ ha₂ hfeq,
    simp only [f] at hfeq,
    simp only [Np, sep_def, mem_filter, mem_range] at ha₁,
    obtain ⟨hna₁, ⟨w₁, hw₁⟩⟩ := ha₁,
    simp only [Np, sep_def, mem_filter, mem_range] at ha₂,
    obtain ⟨hna₂, ⟨w₂, hw₂⟩⟩ := ha₂,
    rw [hw₁, hw₂, nat.mul_div_cancel_left w₁ hp, nat.mul_div_cancel_left w₂ hp] at hfeq,
    have hw₁_eq_w₂ : w₁ = w₂,
    rw [← nat.succ_pred_eq_of_pos (show w₁ > 0, by nlinarith), ← nat.sub_one,
        ← nat.succ_pred_eq_of_pos (show w₂ > 0, by nlinarith), ← nat.sub_one, hfeq],
    rw [(show a₁ = p * w₁ - 1, by finish), (show a₂ = p * w₂ - 1, by finish), hw₁_eq_w₂] },

  calc  card Np ≤ card (range (n / p)) : card_le_card_of_inj_on f hf hf_inj
  ...           = n / p                : card_range (n / p),
end

lemma card_le_div_real {n p : ℕ} (hp : 0 < p) :
  (card {e ∈ range n | p ∣ (e + 1)} : ℝ) ≤ n * (1 / p) :=
begin
  have hp0 : (p : ℝ) > 0 := nat.cast_pos.mpr hp,
  have hnp : (n / p) * p ≤ n := nat.div_mul_le_self n p,
  calc  (card {e ∈ range n | p ∣ (e + 1)} : ℝ)
      ≤ ↑(n / p)      : nat.cast_le.mpr (card_le_div_nat hp)
  ... ≤ ↑n / ↑p       : (le_div_iff hp0).mpr (by assumption_mod_cast)
  ... = ↑n * (1 / ↑p) : div_eq_mul_one_div ↑n ↑p,
end

lemma card_eq_card_sdiff_add_card {A B : finset ℕ} (h : A ⊆ B) :
  (card B) = (card (B \ A)) + (card A) :=
(nat.sub_eq_iff_eq_add (card_le_of_subset h)).mp (eq.symm (card_sdiff h))

lemma lemma1_not_hyp_imp_sum_lt_half
  (h : ¬ tendsto (λ n, ∑ p in { p ∈ range n | nat.prime p }, (1 / (p : ℝ))) at_top at_top) :
  ∃ k, ∀ x, ∑ p in {p ∈ range (x + 1) | p > k ∧ nat.prime p }, 1 / (p : ℝ) < 1 / 2 :=
begin
  have h0 : (λ n, ∑ p in { p ∈ range n | nat.prime p }, (1 / (p : ℝ)))
          = (λ n, ∑ p in range n, ite (nat.prime p) (1 / (p : ℝ)) 0),
  { funext n, rw [sep_def, sum_filter], finish },
  rw h0 at h,

  have hf : ∀ (n : ℕ), 0 ≤ ite (nat.prime n) (1 / (n : ℝ)) 0,
  { intro n, split_ifs,
    { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
    { exact rfl.ge } },

  rw ← summable_iff_not_tendsto_nat_at_top_of_nonneg hf at h,
  rw summable_iff_vanishing at h,
  specialize h (set.Ioo (-1 : ℝ) ((1 : ℝ) / 2)) (mem_nhds_sets is_open_Ioo (by norm_num)),
  obtain ⟨s, h⟩ := h,
  obtain ⟨k, hk⟩ := exists_nat_subset_range s,
  use k,
  intro x,

  set P := {p ∈ range (x + 1) | p > k ∧ nat.prime p } with hP₁,
  have hP₂ : P = filter (λ (p : ℕ), p > k ∧ nat.prime p) (range (x + 1)),
  { rw [hP₁, sep_def], finish },

  specialize h (filter (λ (n : ℕ), n > k) (range (x + 1))) _,
  { rw disjoint_iff_ne,
    intros a ha b hb,
    rw mem_filter at ha,
    obtain ⟨-, hak⟩ := ha,
    exact ne_of_gt (lt_trans (mem_range.mp (hk hb)) hak) },
  rw [← sum_filter, filter_filter, ← hP₂, set.mem_Ioo] at h,

  exact h.right,
end

lemma lemma2_range_x_sdiff_M_eq_U {x k : ℕ} :
  range x \ {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k } =
  finset.bUnion {p ∈ range (x + 1) | p > k ∧ nat.prime p } (λ p, {e ∈ range x | p ∣ (e + 1) }) :=
begin
  ext e,
  simp only [mem_bUnion, not_and, mem_sdiff, sep_def, mem_filter, mem_range],
  push_neg,
  split,
  { rintros ⟨hex, hexh⟩,
    obtain ⟨p, ⟨hpp, hpe1⟩, hpk⟩ := hexh hex,
    use p,
    split,
    { simp only [mem_filter, mem_range],
    refine ⟨_, hpk, hpp⟩,
    calc p ≤ e + 1 : (nat.le_of_dvd (nat.succ_pos e)) hpe1
    ...    < x + 1 : nat.succ_lt_succ hex },
    { exact ⟨hex, hpe1⟩ } },
  { rintros ⟨p, hpfilter, ⟨hex, hpe1⟩⟩,
    simp only [mem_filter, mem_range] at hpfilter,
    obtain ⟨-, hpk, hpp⟩ := hpfilter,
    rw imp_iff_right hex,
    exact ⟨hex, ⟨p, ⟨hpp, hpe1⟩, hpk⟩⟩ },
end

lemma lemma3_card_U_le_x_mul_sum {x k : ℕ} :
  (card
    (finset.bUnion {p ∈ range (x + 1) | p > k ∧ nat.prime p } (λ p, {e ∈ range x | p ∣ (e + 1) }))
  : ℝ)
  ≤ x * (∑ p in {p ∈ range (x + 1) | p > k ∧ nat.prime p }, 1 / p) :=
begin
  let P := {p ∈ range (x + 1) | p > k ∧ nat.prime p },
  let N := (λ p, {e ∈ range x | p ∣ (e + 1) }),
  have h : card (finset.bUnion P N) ≤ ∑ p in P, card (N p) := card_bUnion_le,

  calc  (card (finset.bUnion P N) : ℝ)
      ≤ ∑ p in P, card (N p)  : by assumption_mod_cast
  ... ≤ ∑ p in P, x * (1 / p) : by { refine sum_le_sum _,
                                     intro p,
                                     simp only [P, sep_def, mem_filter, mem_range],
                                     rintros ⟨-, -, hpp⟩,
                                     simp only [N, card_le_div_real (nat.prime.pos hpp)] }
  ... = x * (∑ p in P, 1 / p) : mul_sum.symm,
end

lemma lemma4_aux_card_M1_le_2_pow_k {x k : ℕ} :
  card {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k} ≤ 2 ^ k :=
begin
  let M₁ := {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  set f : finset ℕ → ℕ := λ s, (finset.prod s (λ a, a)) - 1 with hf_def,
  let K := powerset (image nat.succ (range k)),

  have h : M₁ ⊆ image f K,
  { intros m hm,
    simp only [M₁, sep_def, mem_filter, mem_range] at hm,
    obtain ⟨hmx, hms, hmp⟩ := hm,
    have h' : ∃ (a : finset ℕ), a ⊆ image nat.succ (range k) ∧ f a = m,
    { use (m + 1).factors,
      { rw [multiset.coe_nodup, ← nat.squarefree_iff_nodup_factors (nat.succ_ne_zero m)],
        exact hms },
      split,
      { intro p,
        have h1 : p ∈ (m + 1).factors → (∃ (a : ℕ), a < k ∧ a.succ = p),
        { intro hp,
          use p.pred,
          rw (nat.mem_factors (nat.zero_lt_succ m)) at hp,
          exact ⟨lt_of_lt_of_le (nat.pred_lt (nat.prime.ne_zero hp.left)) ((hmp p) hp),
                nat.succ_pred_eq_of_pos (nat.prime.pos hp.left)⟩ },
        simpa },
      { have h2 : (m + 1).factors.prod - 1 = m,
        { rwa nat.prod_factors (nat.zero_lt_succ m), exact nat.succ_sub_one m },
      rw hf_def,
      simpa } },
    simpa },

  calc card M₁ ≤ card (image f K)                    : card_le_of_subset h
  ...          ≤ card K                              : card_image_le
  ...          ≤ 2 ^ card (image nat.succ (range k)) : by simp only [K, card_powerset]
  ...          ≤ 2 ^ card (range k)                  : pow_le_pow one_le_two card_image_le
  ...          = 2 ^ k                               : by rw (card_range k),
end

lemma lemma4_card_M_le_2_pow_k_mul_sqrt_x {x k : ℕ} :
  card {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k } ≤ (2 ^ k) * nat.sqrt(x) :=
begin
  let M := {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k },
  let M₁ := {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let M₂ := {e ∈ range (nat.sqrt x) | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let K := finset.product M₁ M₂,
  let f : ℕ × ℕ → ℕ := λ mn, (mn.2 + 1) ^ 2 * (mn.1 + 1) - 1,

  have h1 : M ⊆ image f K,
  { intros m hm,
    simp only [M, sep_def, mem_filter, mem_range] at hm,
    obtain ⟨hmx, hmp⟩ := hm,
    have h1' : ∃ (a b : ℕ), (a ∈ M₁ ∧ b ∈ M₂) ∧ f (a, b) = m,
    { obtain ⟨a, b, hab₁, hab₂⟩ := nat.sq_mul_squarefree_of_pos' (nat.zero_lt_succ m),

      have h11 : a ∈ M₁,
      { simp only [M₁, sep_def, mem_filter, mem_range],
        have ham : (a + 1) ∣ (m + 1) := dvd.intro_left ((b + 1) ^ 2) hab₁,
        refine ⟨(lt_of_le_of_lt _) hmx, hab₂, _⟩,
        { exact nat.succ_le_succ_iff.mp ((nat.le_of_dvd (nat.zero_lt_succ m)) ham) },
        { intro p,
          specialize hmp p,
          rintros ⟨hpp, hpa⟩,
          exact hmp ⟨hpp, dvd.trans hpa ham⟩ } },

      have h12 : b ∈ M₂,
      { simp only [M₂, sep_def, mem_filter, mem_range],
        have hbm₁ : (b + 1) ^ 2 ∣ (m + 1) := dvd.intro (a + 1) hab₁,
        have hbm₂ : (b + 1) ∣ (m + 1) := nat.dvd_of_pow_dvd one_le_two hbm₁,
        split,
        { calc b < b + 1 : lt_add_one b
          ...    ≤ nat.sqrt(m + 1) : by { rw [nat.le_sqrt, ← pow_two (b + 1)],
                                          exact nat.le_of_dvd (nat.zero_lt_succ m) hbm₁ }
          ...    ≤ nat.sqrt x : nat.sqrt_le_sqrt (nat.succ_le_iff.mpr hmx) },
        { intro p,
          specialize hmp p,
          rintros ⟨hpp, hpb⟩,
          exact hmp ⟨hpp, dvd.trans hpb hbm₂⟩ } },

      have h13 : f (a, b) = m,
      { have h13' : (b + 1) ^ 2 * (a + 1) - 1 = m, rw [hab₁, nat.succ_sub_one m],
        simpa [f] },

      exact ⟨a, b, ⟨h11, h12⟩, h13⟩ },
    simpa },

  have h2 : card M₁ ≤ 2 ^ k := lemma4_aux_card_M1_le_2_pow_k,
  have h3 : card M₂ ≤ nat.sqrt x,
  { rw ← card_range (nat.sqrt x), refine card_le_of_subset _, simp [M₂] },

  calc card M ≤ card (image f K)   : card_le_of_subset h1
  ...         ≤ card K             : card_image_le
  ...         = card M₁ * card M₂  : card_product M₁ M₂
  ...         ≤ 2 ^ k * nat.sqrt x : mul_le_mul' h2 h3,
end

theorem real.tendsto_sum_one_div_prime_at_top :
  tendsto (λ n, ∑ p in { p ∈ range n | nat.prime p }, (1 / (p : ℝ))) at_top at_top :=
begin
  by_contradiction,

  obtain ⟨k, h1⟩ := lemma1_not_hyp_imp_sum_lt_half h,
  set x := (2 ^ (k + 1)) * (2 ^ (k + 1)) with hxk,
  specialize h1 x,

  let P := {p ∈ range (x + 1) | p > k ∧ nat.prime p },
  let M := {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k },
  let N := (λ p, {e ∈ range x | p ∣ (e + 1) }),
  let U := finset.bUnion {p ∈ range (x + 1) | p > k ∧ nat.prime p } N,

  have h2 : x = card U + card M,
  { rw ← card_range x, simp only [U, M, P, N, ← lemma2_range_x_sdiff_M_eq_U],
    exact card_eq_card_sdiff_add_card (by simp [M]) },

  have h3 : (card U : ℝ) < x / 2,
  { calc (card U : ℝ) ≤ x * (∑ p in P, 1 / p) : lemma3_card_U_le_x_mul_sum
    ...               < x * (1 / 2)           : mul_lt_mul_of_pos_left h1 (by norm_num)
    ...               = x / 2                 : mul_one_div x 2 },

  have h4 : (card M : ℝ) ≤ x / 2,
  { have h41 : card M ≤ (2 ^ k) * nat.sqrt(x)           := lemma4_card_M_le_2_pow_k_mul_sqrt_x,
    have h42 : nat.sqrt(x) = 2 ^ (k + 1)                := nat.sqrt_eq (2 ^ (k + 1)),
    have h43 : (x : ℝ) = (2 ^ (k + 1)) * (2 ^ (k + 1)), { assumption_mod_cast },
    calc (card M : ℝ) ≤ ((2 ^ k) * (2 ^ (k + 1)) : ℝ)   : by { rw h42 at h41, assumption_mod_cast }
    ...               = x / 2                           : by { rw h43, ring_exp } },

  refine (lt_self_iff_false (x : ℝ)).mp _,
  calc (x : ℝ) = (card U : ℝ) + (card M : ℝ) : by assumption_mod_cast
  ...          < x / 2 + x / 2               : add_lt_add_of_lt_of_le h3 h4
  ...          = x                           : add_halves ↑x,
end
