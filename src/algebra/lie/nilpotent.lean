/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.solvable
import algebra.lie.quotient
import linear_algebra.eigenspace
import ring_theory.nilpotent

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `lie_module.lower_central_series`
  * `lie_module.is_nilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/

universes u v w w₁ w₂

section nilpotent_modules

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (k : ℕ) (N : lie_submodule R L M)

namespace lie_submodule

/-- A generalisation of the lower central series. The zeroth term is a specified Lie submodule of
a Lie module. In the case when we specify the top ideal `⊤` of the Lie algebra, regarded as a Lie
module over itself, we get the usual lower central series of a Lie algebra.

It can be more convenient to work with this generalisation when considering the lower central series
of a Lie submodule, regarded as a Lie module in its own right, since it provides a type-theoretic
expression of the fact that the terms of the Lie submodule's lower central series are also Lie
submodules of the enclosing Lie module.

See also `lie_module.lower_central_series_eq_lcs_comap` and
`lie_module.lower_central_series_map_eq_lcs` below. -/
def lcs : lie_submodule R L M → lie_submodule R L M := (λ N, ⁅(⊤ : lie_ideal R L), N⁆)^[k]

@[simp] lemma lcs_zero (N : lie_submodule R L M) : N.lcs 0 = N := rfl

@[simp] lemma lcs_succ : N.lcs (k + 1) = ⁅(⊤ : lie_ideal R L), N.lcs k⁆ :=
function.iterate_succ_apply' (λ N', ⁅⊤, N'⁆) k N

end lie_submodule

namespace lie_module

variables (R L M)

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series : lie_submodule R L M := (⊤ : lie_submodule R L M).lcs k

@[simp] lemma lower_central_series_zero : lower_central_series R L M 0 = ⊤ := rfl

@[simp] lemma lower_central_series_succ :
  lower_central_series R L M (k + 1) = ⁅(⊤ : lie_ideal R L), lower_central_series R L M k⁆ :=
(⊤ : lie_submodule R L M).lcs_succ k

end lie_module

namespace lie_submodule

open lie_module

variables {R L M}

lemma lcs_le_self : N.lcs k ≤ N :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lcs_succ],
    exact (lie_submodule.mono_lie_right _ _ ⊤ ih).trans (N.lie_le_right ⊤), },
end

lemma lower_central_series_eq_lcs_comap :
  lower_central_series R L N k = (N.lcs k).comap N.incl :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lcs_succ, lower_central_series_succ] at ⊢ ih,
    have : N.lcs k ≤ N.incl.range,
    { rw N.range_incl,
      apply lcs_le_self, },
    rw [ih, lie_submodule.comap_bracket_eq _ _ N.incl N.ker_incl this], },
end

lemma lower_central_series_map_eq_lcs :
  (lower_central_series R L N k).map N.incl = N.lcs k :=
begin
  rw [lower_central_series_eq_lcs_comap, lie_submodule.map_comap_incl, inf_eq_right],
  apply lcs_le_self,
end

end lie_submodule

namespace lie_module

variables (R L M)

lemma antitone_lower_central_series : antitone $ lower_central_series R L M :=
begin
  intros l k,
  induction k with k ih generalizing l;
  intros h,
  { exact (le_zero_iff.mp h).symm ▸ le_refl _, },
  { rcases nat.of_le_succ h with hk | hk,
    { rw lower_central_series_succ,
      exact (lie_submodule.mono_lie_right _ _ ⊤ (ih hk)).trans (lie_submodule.lie_le_right _ _), },
    { exact hk.symm ▸ le_refl _, }, },
end

lemma trivial_iff_lower_central_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
begin
  split; intros h,
  { erw [eq_bot_iff, lie_submodule.lie_span_le], rintros m ⟨x, n, hn⟩, rw [← hn, h.trivial], simp,},
  { rw lie_submodule.eq_bot_iff at h, apply is_trivial.mk, intros x m, apply h,
    apply lie_submodule.subset_lie_span, use [x, m], refl, },
end

lemma iterate_to_endomorphism_mem_lower_central_series (x : L) (m : M) (k : ℕ) :
  (to_endomorphism R L M x)^[k] m ∈ lower_central_series R L M k :=
begin
  induction k with k ih,
  { simp only [function.iterate_zero], },
  { simp only [lower_central_series_succ, function.comp_app, function.iterate_succ',
      to_endomorphism_apply_apply],
    exact lie_submodule.lie_mem_lie _ _ (lie_submodule.mem_top x) ih, },
end

variables {R L M}

lemma map_lower_central_series_le
  {M₂ : Type w₁} [add_comm_group M₂] [module R M₂] [lie_ring_module L M₂] [lie_module R L M₂]
  (k : ℕ) (f : M →ₗ⁅R,L⁆ M₂) :
  lie_submodule.map f (lower_central_series R L M k) ≤ lower_central_series R L M₂ k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.map_bracket_eq],
    exact lie_submodule.mono_lie_right _ _ ⊤ ih, },
end

variables (R L M)
open lie_algebra

lemma derived_series_le_lower_central_series (k : ℕ) :
  derived_series R L k ≤ lower_central_series R L L k :=
begin
  induction k with k h,
  { rw [derived_series_def, derived_series_of_ideal_zero, lower_central_series_zero],
    exact le_refl _, },
  { have h' : derived_series R L k ≤ ⊤, { by simp only [le_top], },
    rw [derived_series_def, derived_series_of_ideal_succ, lower_central_series_succ],
    exact lie_submodule.mono_lie _ _ _ _ h' h, },
end

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class is_nilpotent : Prop :=
(nilpotent : ∃ k, lower_central_series R L M k = ⊥)

@[priority 100]
instance trivial_is_nilpotent [is_trivial L M] : is_nilpotent R L M :=
⟨by { use 1, change ⁅⊤, ⊤⁆ = ⊥, simp, }⟩

lemma nilpotent_endo_of_nilpotent_module [hM : is_nilpotent R L M] :
  ∃ (k : ℕ), ∀ (x : L), (to_endomorphism R L M x)^k = 0 :=
begin
  unfreezingI { obtain ⟨k, hM⟩ := hM, },
  use k,
  intros x, ext m,
  rw [linear_map.pow_apply, linear_map.zero_apply, ← @lie_submodule.mem_bot R L M, ← hM],
  exact iterate_to_endomorphism_mem_lower_central_series R L M x m k,
end

/-- For a nilpotent Lie module, the weight space of the 0 weight is the whole module.

This result will be used downstream to show that weight spaces are Lie submodules, at which time
it will be possible to state it in the language of weight spaces. -/
lemma infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L M] :
  (⨅ (x : L), (to_endomorphism R L M x).maximal_generalized_eigenspace 0) = ⊤ :=
begin
  ext m,
  simp only [module.End.mem_maximal_generalized_eigenspace, submodule.mem_top, sub_zero, iff_true,
    zero_smul, submodule.mem_infi],
  intros x,
  obtain ⟨k, hk⟩ := nilpotent_endo_of_nilpotent_module R L M,
  use k, rw hk,
  exact linear_map.zero_apply m,
end

/-- If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `lie_algebra.nilpotent_of_nilpotent_quotient`
below for the corresponding result for Lie algebras. -/
lemma nilpotent_of_nilpotent_quotient {N : lie_submodule R L M}
  (h₁ : N ≤ max_triv_submodule R L M) (h₂ : is_nilpotent R L (M ⧸ N)) : is_nilpotent R L M :=
begin
  unfreezingI { obtain ⟨k, hk⟩ := h₂, },
  use k+1,
  simp only [lower_central_series_succ],
  suffices : lower_central_series R L M k ≤ N,
  { replace this := lie_submodule.mono_lie_right _ _ ⊤ (le_trans this h₁),
    rwa [ideal_oper_max_triv_submodule_eq_bot, le_bot_iff] at this, },
  rw [← lie_submodule.quotient.map_mk'_eq_bot_le, ← le_bot_iff, ← hk],
  exact map_lower_central_series_le k (lie_submodule.quotient.mk' N),
end

/-- Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0. -/
noncomputable def nilpotency_length : ℕ :=
Inf { k | lower_central_series R L M k = ⊥ }

lemma nilpotency_length_eq_zero_iff [is_nilpotent R L M] :
  nilpotency_length R L M = 0 ↔ subsingleton M :=
begin
  let s := { k | lower_central_series R L M k = ⊥ },
  have hs : s.nonempty,
  { unfreezingI { obtain ⟨k, hk⟩ := (by apply_instance : is_nilpotent R L M), },
    exact ⟨k, hk⟩, },
  change Inf s = 0 ↔ _,
  rw [← lie_submodule.subsingleton_iff R L M, ← subsingleton_iff_bot_eq_top,
      ← lower_central_series_zero, @eq_comm (lie_submodule R L M)],
  refine ⟨λ h, h ▸ nat.Inf_mem hs, λ h, _⟩,
  rw nat.Inf_eq_zero,
  exact or.inl h,
end

lemma nilpotency_length_eq_succ_iff (k : ℕ) :
  nilpotency_length R L M = k + 1 ↔
  lower_central_series R L M (k + 1) = ⊥ ∧ lower_central_series R L M k ≠ ⊥ :=
begin
  let s := { k | lower_central_series R L M k = ⊥ },
  change Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s,
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s,
  { rintros k₁ k₂ h₁₂ (h₁ : lower_central_series R L M k₁ = ⊥),
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lower_central_series R L M h₁₂), },
  exact nat.Inf_upward_closed_eq_succ_iff hs k,
end

/-- Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`. -/
noncomputable def lower_central_series_last : lie_submodule R L M :=
match nilpotency_length R L M with
| 0     := ⊥
| k + 1 := lower_central_series R L M k
end

lemma lower_central_series_last_le_max_triv :
  lower_central_series_last R L M ≤ max_triv_submodule R L M :=
begin
  rw lower_central_series_last,
  cases h : nilpotency_length R L M with k,
  { exact bot_le, },
  { rw le_max_triv_iff_bracket_eq_bot,
    rw [nilpotency_length_eq_succ_iff, lower_central_series_succ] at h,
    exact h.1, },
end

lemma nontrivial_lower_central_series_last [nontrivial M] [is_nilpotent R L M] :
  nontrivial (lower_central_series_last R L M) :=
begin
  rw [lie_submodule.nontrivial_iff_ne_bot, lower_central_series_last],
  cases h : nilpotency_length R L M,
  { rw [nilpotency_length_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h,
    contradiction, },
  { rw nilpotency_length_eq_succ_iff at h,
    exact h.2, },
end

lemma nontrivial_max_triv_of_is_nilpotent [nontrivial M] [is_nilpotent R L M] :
  nontrivial (max_triv_submodule R L M) :=
set.nontrivial_mono
  (lower_central_series_last_le_max_triv R L M)
  (nontrivial_lower_central_series_last R L M)

lemma is_nilpotent_iff_range_to_endomorphism :
  is_nilpotent R L M ↔ is_nilpotent R (to_endomorphism R L M).range M :=
begin
  suffices : ∀ k, (lower_central_series R L M k : submodule R M) =
                  (lower_central_series R (to_endomorphism R L M).range M k : submodule R M),
  { split;
    rintros ⟨k, hk⟩;
    use k;
    rw ← lie_submodule.coe_to_submodule_eq_iff at ⊢ hk,
    { rwa ← this, },
    { rwa this, }, },
  intros,
  induction k with k ih,
  { simp, },
  { simp only [lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span',
      ← (lower_central_series R (to_endomorphism R L M).range M k).mem_coe_submodule, ← ih],
    congr,
    ext m,
    split,
    { rintros ⟨x, hx, n, hn, rfl⟩,
      exact ⟨⟨to_endomorphism R L M x, lie_hom.mem_range_self _ x⟩, lie_submodule.mem_top _,
        n, hn, rfl⟩, },
    { rintros ⟨⟨-, ⟨y, rfl⟩⟩, -, n, hn, rfl⟩,
      exact ⟨y, lie_submodule.mem_top _, n, hn, rfl⟩, }, },
end

end lie_module

end nilpotent_modules

@[priority 100]
instance lie_algebra.is_solvable_of_is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [hL : lie_module.is_nilpotent R L L] :
  lie_algebra.is_solvable R L :=
begin
  obtain ⟨k, h⟩ : ∃ k, lie_module.lower_central_series R L L k = ⊥ := hL.nilpotent,
  use k, rw ← le_bot_iff at h ⊢,
  exact le_trans (lie_module.derived_series_le_lower_central_series R L k) h,
end

section nilpotent_algebras

variables (R : Type u) (L : Type v) (L' : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbreviation lie_algebra.is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] : Prop :=
lie_module.is_nilpotent R L L

open lie_algebra

lemma lie_algebra.nilpotent_ad_of_nilpotent_algebra [is_nilpotent R L] :
  ∃ (k : ℕ), ∀ (x : L), (ad R L x)^k = 0 :=
lie_module.nilpotent_endo_of_nilpotent_module R L L

/-- See also `lie_algebra.zero_root_space_eq_top_of_nilpotent`. -/
lemma lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L] :
  (⨅ (x : L), (ad R L x).maximal_generalized_eigenspace 0) = ⊤ :=
lie_module.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L L

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.

variables {R L L'}

open lie_module (lower_central_series)

/-- Given an ideal `I` of a Lie algebra `L`, the lower central series of `L ⧸ I` is the same
whether we regard `L ⧸ I` as an `L` module or an `L ⧸ I` module.

TODO: This result obviously generalises but the generalisation requires the missing definition of
morphisms between Lie modules over different Lie algebras. -/
lemma coe_lower_central_series_ideal_quot_eq {I : lie_ideal R L} (k : ℕ) :
  (lower_central_series R L (L ⧸ I) k : submodule R (L ⧸ I)) =
  lower_central_series R (L ⧸ I) (L ⧸ I) k :=
begin
  induction k with k ih,
  { simp only [lie_submodule.top_coe_submodule, lie_module.lower_central_series_zero], },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span],
    congr,
    ext x,
    split,
    { rintros ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
      erw [← lie_submodule.mem_coe_submodule, ih, lie_submodule.mem_coe_submodule] at hz,
      exact ⟨⟨lie_submodule.quotient.mk y, submodule.mem_top⟩, ⟨z, hz⟩, rfl⟩, },
    { rintros ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
      erw [← lie_submodule.mem_coe_submodule, ← ih, lie_submodule.mem_coe_submodule] at hz,
      exact ⟨⟨y, submodule.mem_top⟩, ⟨z, hz⟩, rfl⟩, }, },
end

/-- Note that the below inequality can be strict. For example the ideal of strictly-upper-triangular
2x2 matrices inside the Lie algebra of upper-triangular 2x2 matrices with `k = 1`. -/
lemma coe_lower_central_series_ideal_le {I : lie_ideal R L} (k : ℕ) :
  (lower_central_series R I I k : submodule R I) ≤ lower_central_series R L I k :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span],
    apply submodule.span_mono,
    rintros x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
    exact ⟨⟨y.val, submodule.mem_top⟩, ⟨z, ih hz⟩, rfl⟩, },
end

/-- A central extension of nilpotent Lie algebras is nilpotent. -/
lemma lie_algebra.nilpotent_of_nilpotent_quotient {I : lie_ideal R L}
  (h₁ : I ≤ center R L) (h₂ : is_nilpotent R (L ⧸ I)) : is_nilpotent R L :=
begin
  suffices : lie_module.is_nilpotent R L (L ⧸ I),
  { exact lie_module.nilpotent_of_nilpotent_quotient R L L h₁ this, },
  unfreezingI { obtain ⟨k, hk⟩ := h₂, },
  use k,
  simp [← lie_submodule.coe_to_submodule_eq_iff, coe_lower_central_series_ideal_quot_eq, hk],
end

lemma lie_algebra.non_trivial_center_of_is_nilpotent [nontrivial L] [is_nilpotent R L] :
  nontrivial $ center R L :=
lie_module.nontrivial_max_triv_of_is_nilpotent R L L

lemma lie_ideal.map_lower_central_series_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
  lie_ideal.map f (lower_central_series R L L k) ≤ lower_central_series R L' L' k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ],
    exact le_trans (lie_ideal.map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ le_top ih), },
end

lemma lie_ideal.lower_central_series_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'}
  (h : function.surjective f) :
  lie_ideal.map f (lower_central_series R L L k) = lower_central_series R L' L' k :=
begin
  have h' : (⊤ : lie_ideal R L).map f = ⊤,
  { rw ←f.ideal_range_eq_map,
    exact f.ideal_range_eq_top_of_surjective h, },
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero], exact h', },
  { simp only [lie_module.lower_central_series_succ, lie_ideal.map_bracket_eq f h, ih, h'], },
end

lemma function.injective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L'] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.injective f) : is_nilpotent R L :=
{ nilpotent :=
  begin
    obtain ⟨k, hk⟩ := id h₁,
    use k,
    apply lie_ideal.bot_of_map_eq_bot h₂, rw [eq_bot_iff, ← hk],
    apply lie_ideal.map_lower_central_series_le,
  end, }

lemma function.surjective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.surjective f) : is_nilpotent R L' :=
{ nilpotent :=
  begin
    obtain ⟨k, hk⟩ := id h₁,
    use k,
    rw [← lie_ideal.lower_central_series_map_eq k h₂, hk],
    simp only [lie_ideal.map_eq_bot_iff, bot_le],
  end, }

lemma lie_equiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
  is_nilpotent R L ↔ is_nilpotent R L' :=
begin
  split; introsI h,
  { exact e.symm.injective.lie_algebra_is_nilpotent, },
  { exact e.injective.lie_algebra_is_nilpotent, },
end

lemma lie_hom.is_nilpotent_range [is_nilpotent R L] (f : L →ₗ⁅R⁆ L') :
  is_nilpotent R f.range :=
f.surjective_range_restrict.lie_algebra_is_nilpotent

lemma lie_algebra.is_nilpotent_iff_range_ad :
  is_nilpotent R L ↔ is_nilpotent R (ad R L).range :=
begin
  refine ⟨_, λ h, _⟩,
  { introsI h,
    exact (ad R L).is_nilpotent_range, },
  { have : (ad R L).ker = center R L, { by simp, },
    exact lie_algebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
      ((ad R L).quot_ker_equiv_range.nilpotent_iff_equiv_nilpotent.mpr h), },
end

instance [h : lie_algebra.is_nilpotent R L] : lie_algebra.is_nilpotent R (⊤ : lie_subalgebra R L) :=
lie_subalgebra.top_equiv_self.nilpotent_iff_equiv_nilpotent.mpr h

end nilpotent_algebras

section of_associative

variables (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A]

lemma lie_algebra.ad_nilpotent_of_nilpotent {a : A} (h : is_nilpotent a) :
  is_nilpotent (lie_algebra.ad R A a) :=
begin
  rw lie_algebra.ad_eq_lmul_left_sub_lmul_right,
  have hl : is_nilpotent (algebra.lmul_left R a), { rwa algebra.is_nilpotent_lmul_left_iff, },
  have hr : is_nilpotent (algebra.lmul_right R a), { rwa algebra.is_nilpotent_lmul_right_iff, },
  exact (algebra.commute_lmul_left_right R a a).is_nilpotent_sub hl hr,
end

variables {R}

lemma lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad {L : Type v} [lie_ring L] [lie_algebra R L]
  (K : lie_subalgebra R L) {x : K} (h : is_nilpotent (lie_algebra.ad R L ↑x)) :
  is_nilpotent (lie_algebra.ad R K x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  exact linear_map.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn,
end

lemma lie_algebra.is_nilpotent_ad_of_is_nilpotent {L : lie_subalgebra R A} {x : L}
  (h : is_nilpotent (x : A)) : is_nilpotent (lie_algebra.ad R L x) :=
L.is_nilpotent_ad_of_is_nilpotent_ad $ lie_algebra.ad_nilpotent_of_nilpotent R h

end of_associative

namespace lie_ideal

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (I : lie_ideal R L) (k : ℕ)

-- @[simp] lemma sigh : comap I.incl (⊤ : lie_ideal R L) = ⊤ :=
-- begin
--   simp only [← lie_submodule.coe_to_submodule_eq_iff, comap_coe_submodule,
--     lie_submodule.top_coe_submodule, submodule.comap_top],
-- end

open lie_module

def lcs : lie_ideal R L := (λ J, ⁅I, J⁆)^[k] I

@[simp] lemma lcs_zero : I.lcs 0 = I := rfl

@[simp] lemma lcs_succ : I.lcs (k + 1) = ⁅I, I.lcs k⁆ :=
function.iterate_succ_apply' (λ J, ⁅I, J⁆) k I

lemma lcs_top : (⊤ : lie_ideal R L).lcs k = lower_central_series R L L k := rfl

lemma lcs_le_self : I.lcs k ≤ I :=
begin
  cases k,
  { simp, },
  { simp only [lcs_succ],
    apply I.lie_le_left, },
end

lemma lower_central_series_eq_lcs_comap :
  lower_central_series R I I k = (I.lcs k).comap I.incl :=
begin
  induction k with k ih,
  { simp, },
  { simp [lower_central_series_succ, lcs_succ, ih,
      ← comap_bracket_incl_of_le _ (le_refl I) (I.lcs_le_self k)], },
end

lemma map_lower_central_series_eq_lcs :
  lie_ideal.map I.incl (lower_central_series R I I k) = I.lcs k :=
begin
  rw [lower_central_series_eq_lcs_comap, map_comap_incl, inf_eq_right],
  exact lcs_le_self I k,
end

end lie_ideal

section foo

variables {R L : Type*} [comm_ring R] [lie_ring L] [lie_algebra R L]
open lie_algebra lie_module (hiding is_nilpotent)

lemma submodule.span_foo {M : Type*} [add_comm_group M] [module R M]
  {p : submodule R M} {s : set M} :
  p ⊔ submodule.span R s = submodule.span R (p ∪ s) :=
by rw [submodule.span_union, p.span_eq]

variables (I : lie_ideal R L)
variables (M : Type*) [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables (k : ℕ)

namespace lie_ideal

def lcs' : lie_submodule R L M := (λ N, ⁅I, N⁆)^[k] ⊤

@[simp] lemma lcs'_zero : I.lcs' M 0 = ⊤ := rfl

@[simp] lemma lcs'_succ : I.lcs' M (k + 1) = ⁅I, I.lcs' M k⁆ :=
function.iterate_succ_apply' (λ N, ⁅I, N⁆) k ⊤

lemma lcs'_top : (⊤ : lie_ideal R L).lcs' M k = lower_central_series R L M k := rfl

lemma coe_lcs'_eq : (I.lcs' M k : submodule R M) = lower_central_series R I M k :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lower_central_series_succ, lcs'_succ, lie_submodule.lie_ideal_oper_eq_linear_span],
    -- Really be a job for `exists_congr₂`
    congr,
    ext m,
    split,
    { rintros ⟨⟨x, hx : x ∈ I⟩, ⟨n, hn : n ∈ I.lcs' M k⟩, rfl⟩,
      simp only [set_like.coe_mk, lie_subalgebra.coe_bracket_of_module],
      rw [← lie_submodule.mem_coe_submodule, ih, lie_submodule.mem_coe_submodule] at hn,
      refine ⟨⟨⟨x, hx⟩, submodule.mem_top⟩, ⟨n, hn⟩, rfl⟩, },
    { rintros ⟨⟨⟨x, hx : x ∈ I⟩, hx'⟩, ⟨n, hn : n ∈ lower_central_series R I M k⟩, rfl⟩,
      simp only [set_like.coe_mk, lie_subalgebra.coe_bracket_of_module],
      rw [← lie_submodule.mem_coe_submodule, ← ih, lie_submodule.mem_coe_submodule] at hn,
      exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, }, },
end

end lie_ideal

variables {I M}

@[simp] lemma blah' {N : lie_submodule R L M} {x : L} :
  (N : submodule R M).map (to_endomorphism R L M x) ≤ N :=
begin
  rintros x ⟨y, hy, rfl⟩,
  exact N.lie_mem hy,
end

lemma qux {x : L} {n i j : ℕ} (hx₁ : (R ∙ x) ⊔ I = ⊤) (hx₂ : (to_endomorphism R L M x)^n = 0)
  (hIM : lower_central_series R L M i ≤ I.lcs' M j) :
  lower_central_series R L M (i + n) ≤ I.lcs' M (j + 1) :=
begin
  have : ∀ (N : lie_submodule R L M), (↑⁅(⊤ : lie_ideal R L), N⁆ : submodule R M) =
    (N : submodule R M).map (to_endomorphism R L M x) ⊔ (↑⁅I, N⁆ : submodule R M),
  { intros N,
    simp only [lie_submodule.lie_ideal_oper_eq_linear_span],

    apply le_antisymm,
    { rw submodule.span_le,
      rintros z ⟨⟨y, hy : y ∈ ⊤⟩, ⟨y', hy' : y' ∈ N⟩, rfl⟩,
      simp only [set_like.coe_mk, set_like.mem_coe, submodule.mem_sup, exists_prop,
        submodule.mem_map, exists_exists_and_eq_and, lie_submodule.mem_coe_submodule, ad_apply],
      simp only [← hx₁, submodule.mem_sup, submodule.mem_span_singleton] at hy,
      obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy,
      refine ⟨t • y', (N : lie_submodule R L M).smul_mem' t hy', ⁅z, y'⁆,
        submodule.subset_span ⟨⟨z, hz⟩, ⟨y', hy'⟩, rfl⟩, by simp⟩, },
    { -- This branch does not use `hx₁`: break out?
      rw submodule.span_foo,
      apply submodule.span_mono,
      intros z hz,
      simp only [set.mem_image, set_like.mem_coe, lie_submodule.mem_coe_submodule, ad_apply,
        submodule.map_coe, set.mem_union_eq, set.mem_set_of_eq] at hz,
      rcases hz with ⟨y, hy, rfl⟩ | ⟨⟨y, hy⟩, y', rfl⟩,
      { exact ⟨⟨x, submodule.mem_top⟩, ⟨y, hy⟩, rfl⟩, },
      { exact ⟨⟨y, submodule.mem_top⟩, y', rfl⟩, }, }, },

  suffices : ∀ l, ((⊤ : lie_ideal R L).lcs' M (i + l) : submodule R M) ≤
    (I.lcs' M j : submodule R M).map ((to_endomorphism R L M x)^l) ⊔ (I.lcs' M (j + 1) : submodule R M),
  { simpa only [bot_sup_eq, lie_ideal.incl_coe, submodule.map_zero, hx₂] using this n, },
  intros l,
  induction l with l ih,
  { simp only [add_zero, lie_ideal.lcs'_succ, pow_zero, linear_map.one_eq_id, submodule.map_id],
    exact le_sup_of_le_left hIM, },
  { simp only [lie_ideal.lcs'_succ, i.add_succ l, this, sup_le_iff],
    refine ⟨(submodule.map_mono ih).trans _, le_sup_of_le_right _⟩,
    { rw [submodule.map_sup, ← submodule.map_comp, ← linear_map.mul_eq_comp, ← pow_succ,
        ← I.lcs'_succ],
      exact sup_le_sup_left blah' _, },
    { refine le_trans (lie_submodule.mono_lie_right _ _ I _) (lie_submodule.mono_lie_right _ _ I hIM),
      exact lie_module.antitone_lower_central_series R L M le_self_add, }, },
end

lemma baz {x : L} (hx₁ : (R ∙ x) ⊔ I = ⊤)
  (hx₂ : is_nilpotent $ to_endomorphism R L M x) (hIM : lie_module.is_nilpotent R I M) :
  lie_module.is_nilpotent R L M :=
begin
  obtain ⟨n, hn⟩ := hx₂,
  unfreezingI { obtain ⟨k, hk⟩ := hIM, },
  have hk' : I.lcs' M k = ⊥,
  { simp only [← lie_submodule.coe_to_submodule_eq_iff, I.coe_lcs'_eq, hk,
      lie_submodule.bot_coe_submodule], },
  clear hk, rename hk' hk,
  suffices : ∀ l, lower_central_series R L M (l * n) ≤ I.lcs' M l,
  { use k * n,
    simpa [hk] using this k, },
  intros l,
  induction l with l ih,
  { simp, },
  { exact (l.succ_mul n).symm ▸ qux hx₁ hn ih, },
end

end foo
