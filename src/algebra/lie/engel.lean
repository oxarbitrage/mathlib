/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.cartan_subalgebra

/-!
# Engel's theorem

Foo bar

## Main definitions

  * `is_engelian`
  * `lie_module.is_engelian_of_is_noetherian`
  * `lie_algebra.is_nilpotent_iff`

-/

namespace submodule

-- variables {R M : Type*} [semiring R] [add_comm_monoid M] [module R M] (p : submodule R M)
variables {R M : Type*} [ring R] [add_comm_group M] [module R M] (p : submodule R M)

@[simp] lemma map_span_singleton (x : p) :
  map p.subtype (R ∙ x) = R ∙ (x : M) :=
begin
  apply le_antisymm,
  { rw le_span_singleton_iff,
    intros v hv,
    simp only [subtype_apply, mem_map, mem_span_singleton] at hv,
    obtain ⟨⟨y, hy⟩, ⟨t, ht⟩, rfl⟩ := hv,
    use t,
    rw ← ht,
    refl, },
  { simp only [span_singleton_le_iff_mem, subtype_apply, exists_eq_right, mem_map,
      set_like.coe_eq_coe, mem_span_singleton_self], },
end

variables {p} {q : submodule R M}

@[simp] lemma map_subtype_of_le_range (h : p ≤ q) :
  map q.subtype (of_le h).range = p :=
by conv_rhs { rw [← p.map_subtype_top, ← subtype_comp_of_le p q h, map_comp, map_top], }

end submodule

open lie_module (hiding is_nilpotent)

def is_engelian (R L : Type*) [comm_ring R] [lie_ring L] [lie_algebra R L] : Prop :=
  ∀ (M : Type*) [add_comm_group M], by exactI ∀ [module R M] [lie_ring_module L M], by exactI ∀
    [lie_module R L M], by exactI ∀ (h : ∀ (x : L), is_nilpotent (to_endomorphism R L M x)),
    lie_module.is_nilpotent R L M

lemma is_engelian_iff_equiv_is_engelian {R L₁ L₂ : Type*}
  [comm_ring R] [lie_ring L₁] [lie_algebra R L₁] [lie_ring L₂] [lie_algebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) :
  is_engelian R L₁ ↔ is_engelian R L₂ :=
sorry

variables (R L : Type*) [comm_ring R] [lie_ring L] [lie_algebra R L]

lemma yawn (M : Type*) [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M] :
  lie_module.is_nilpotent R L M ↔ lie_module.is_nilpotent R (⊤ : lie_subalgebra R L) M :=
sorry

lemma is_engelian_of_subsingleton [subsingleton L] : is_engelian R L :=
begin
  introsI M _i1 _i2 _i3 _i4 h,
  have : (⊤ : lie_ideal R L) = ⊥, {
    rw ← lie_submodule.subsingleton_iff R L L at _inst_4,
    resetI,
    apply subsingleton.elim, },
  use 1,
  simp [this],
end

instance : subsingleton (⊥ : lie_subalgebra R L) :=
⟨begin
  rintros ⟨x, hx : x ∈ ⊥⟩ ⟨y, hy : y ∈ ⊥⟩,
  simp only [submodule.mem_bot] at hx hy,
  simp only [subtype.mk_eq_mk, hx, hy],
end⟩

lemma key {K : lie_subalgebra R L} (hK₁ : is_engelian R K) (hK₂ : K < K.normalizer) :
  ∃ (K' : lie_subalgebra R L) (hK' : is_engelian R K'), K < K' :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := set_like.exists_of_lt hK₂,
  let K' : lie_subalgebra R L :=
  { lie_mem' := λ y z hy hz,
    begin
      simp only [set_like.mem_coe, submodule.mem_carrier] at hy hz ⊢,
      rw submodule.mem_sup at hy hz,
      obtain ⟨u, hu, v, hv : v ∈ K, rfl⟩ := hy,
      obtain ⟨t, rfl⟩ := submodule.mem_span_singleton.mp hu,
      obtain ⟨u, hu, w, hw : w ∈ K, rfl⟩ := hz,
      obtain ⟨s, rfl⟩ := submodule.mem_span_singleton.mp hu,
      apply submodule.mem_sup_right,
      simp only [lie_subalgebra.mem_coe_submodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
        lie_smul, lie_self],
      refine K.add_mem (K.smul_mem s _) (K.add_mem (K.smul_mem t _) (K.lie_mem hv hw)),
      { exact (K.mem_normalizer_iff' x).mp hx₁ v hv, },
      { exact (K.mem_normalizer_iff x).mp hx₁ w hw, },
    end,
    .. (R ∙ x) ⊔ (K : submodule R L) },
  have hxK' : x ∈ K',
  { apply submodule.mem_sup_left,
    apply submodule.subset_span,
    simp only [set.mem_singleton], },
  have hKK' : K ≤ K',
  { rw ← lie_subalgebra.coe_submodule_le_coe_submodule,
    exact le_sup_right, },
  have hK' : K' ≤ K.normalizer,
  { rw ← lie_subalgebra.coe_submodule_le_coe_submodule,
    refine sup_le _ (le_of_lt hK₂),
    rw submodule.span_singleton_le_iff_mem, -- This lemma should be `simp`?
    exact hx₁, },
  refine ⟨K', _, _⟩,
  { introsI M _i1 _i2 _i3 _i4 h,
    obtain ⟨I, hI₁⟩ := lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer hKK' hK',
    have hI₂ : (R ∙ (⟨x, hxK'⟩ : K')) ⊔ I = ⊤,
    { rw [← lie_ideal.coe_to_lie_subalgebra_to_submodule R K' I, hI₁],
      have foo : function.injective (K' : submodule R L).subtype,
      { rintros ⟨a⟩ ⟨b⟩ (rfl : a = b), rw subtype.mk_eq_mk, },
      apply submodule.map_injective_of_injective foo,
      simpa, },
    apply baz hI₂ (h _),
    have hI₃ : is_engelian R I,
    { have e : K ≃ₗ⁅R⁆ I := (lie_subalgebra.equiv_of_le hKK').trans
        (lie_equiv.of_eq _ _ ((lie_subalgebra.coe_set_eq _ _).mpr hI₁.symm)),
      rw ← is_engelian_iff_equiv_is_engelian e,
      exact hK₁, },
    exact hI₃ _ (λ x, h x), },
  { rw lt_iff_le_and_ne,
    exact ⟨hKK', λ contra, hx₂ (contra.symm ▸ hxK')⟩, },
end

-- TODO (maybe) Generalise to quotient of any Lie module by a Lie submodule.
lemma boring {K : lie_subalgebra R L} (x : K) (hx : is_nilpotent (lie_algebra.ad R L x)) :
  is_nilpotent (to_endomorphism R K (L ⧸ K.to_lie_submodule) x) :=
module.End.is_nilpotent_mapq hx _

/-- A general form of *Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`lie_module.nontrivial_max_triv_of_is_nilpotent` and `lie_algebra.is_nilpotent_iff`. -/
lemma is_engelian_of_is_noetherian [is_noetherian R L] : is_engelian R L :=
begin
  introsI M _i1 _i2 _i3 _i4 h,
  rw is_nilpotent_iff_range_to_endomorphism,
  let L' := (to_endomorphism R L M).range,
  change lie_module.is_nilpotent R L' M,
  let s := { K : lie_subalgebra R L' | is_engelian R K },
  have hs : s.nonempty := ⟨⊥, is_engelian_of_subsingleton R (⊥ : lie_subalgebra R L')⟩,
  have : ∀ (K ∈ s), K ≠ ⊤ → ∃ (K' ∈ s), K < K',
  { rintros K (hK₁ : is_engelian R K) hK₂,
    haveI : nontrivial (L' ⧸ K.to_lie_submodule),
    { have hK₂' : K.to_lie_submodule ≠ ⊤,
      { rwa [ne.def, ← lie_submodule.coe_to_submodule_eq_iff, K.coe_to_lie_submodule,
          lie_submodule.top_coe_submodule, ← lie_subalgebra.top_coe_submodule,
          K.coe_to_submodule_eq_iff, ← ne.def], },
      rw [ne.def, ← lie_submodule.coe_to_submodule_eq_iff, ← ne.def] at hK₂',
      exact submodule.quotient.nontrivial_of_lt_top _ hK₂'.lt_top, },
    haveI : lie_module.is_nilpotent R K (L' ⧸ K.to_lie_submodule),
    { apply hK₁,
      have h' : ∀ (y : L'), is_nilpotent (y : module.End R M),
      { rintros ⟨-, ⟨y, rfl⟩⟩,
        simp [h y], },
      have h'' : ∀ (y : L'), is_nilpotent (lie_algebra.ad R L' y) :=
        λ y, lie_algebra.is_nilpotent_ad_of_is_nilpotent (h' y),
      intros x,
      apply boring,
      apply h'', },
    apply key R L' hK₁,
    apply lt_of_le_of_ne K.le_normalizer,
    rw [ne.def, eq_comm, K.normalizer_eq_self_iff, ← ne.def,
      ← lie_submodule.nontrivial_iff_ne_bot R K],
    exact lie_module.nontrivial_max_triv_of_is_nilpotent R K (L' ⧸ K.to_lie_submodule), },
  haveI _i5 : is_noetherian R L',
  { apply is_noetherian_of_surjective L (to_endomorphism R L M : L →ₗ[R] module.End R M).range_restrict,
    simp, },
  obtain ⟨K, hK₁, hK₂⟩ := well_founded.well_founded_iff_has_max'.mp
    (lie_subalgebra.well_founded_of_noetherian R L') s hs,
  suffices : ⊤ ∈ s,
  { specialize this M,
    rw yawn,
    apply this,
    rintros ⟨⟨x, ⟨y, rfl⟩⟩, hy⟩,
    have foo : ∀ (x : (⊤ : lie_subalgebra R L')), to_endomorphism R (⊤ : lie_subalgebra R L') M x =
                                                 (x : module.End R M),
    { intros x, ext m, simp [lie_eq_smul], },
    simp [foo, h], },
  convert hK₁,
  symmetry,
  by_contra contra,
  obtain ⟨K', hK'₁, hK'₂⟩ := this K hK₁ contra,
  specialize hK₂ K' hK'₁ (le_of_lt hK'₂),
  rwa [hK₂, lt_self_iff_false] at hK'₂,
end

/-- The specialisation of *Engel's theorem* to Lie algebras. -/
lemma lie_algebra.is_nilpotent_iff [is_noetherian R L] :
  lie_algebra.is_nilpotent R L ↔ ∀ x, is_nilpotent $ lie_algebra.ad R L x :=
⟨λ h x, begin
  haveI := h,
  obtain ⟨k, hk⟩ := lie_algebra.nilpotent_ad_of_nilpotent_algebra R L,
  exact ⟨k, hk x⟩,
end,
λ h, is_engelian_of_is_noetherian R L L h⟩
