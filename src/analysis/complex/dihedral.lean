/-
Copyright (c) 2021 Shadman Sakib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shadman Sakib
-/
import group_theory.specific_groups.dihedral
import analysis.special_functions.trigonometric

/-! # Realization of the dihedral group as isometries of ℂ

The definition `dihedral_to_complex_hom` provides the canonical homomorphism of the dihedral group
into the linear isometries of ℂ. -/

noncomputable theory

open complex dihedral_group

local notation `π` := real.pi

variables (m : ℕ) [fact (0 < m)]

/-- The additive homomorphism embedding `zmod m` in the group of real numbers modulo `2 * π`. -/
def zmod_to_angle : zmod m →+ real.angle :=
zmod.lift m ⟨gmultiples_hom real.angle ↑(2 * π /m),
  begin
    suffices : m • (2 * π / ↑m) = 2 * π,
    { simpa using congr_arg (coe : _ → real.angle) this },
    have : (m:ℝ) ≠ 0 := by exact_mod_cast (fact.out _ : 0 < m).ne',
    field_simp,
    ring,
  end⟩

/-- A function mapping `dihedral_group` to linear isometries of ℂ.
Auxiliary construction for `dihedral_to_complex_hom`. -/
def dihedral_to_complex : dihedral_group m → ℂ ≃ₗᵢ[ℝ] ℂ
| (r i) := rotation (angle_to_circle (zmod_to_angle m i))
| (sr i) := conj_lie * rotation (angle_to_circle (zmod_to_angle m i))

variables {m}

lemma mul_1 (i j : zmod m) : dihedral_to_complex m (r i) * dihedral_to_complex m (r j) =
  dihedral_to_complex m (r (i + j)) :=
begin
  simp only [dihedral_to_complex],
  rw (zmod_to_angle m).map_add,
  rw angle_to_circle_add,
  rw rotation.map_mul,
end

lemma mul_2 (i j : zmod m) : dihedral_to_complex m (r i) * dihedral_to_complex m (sr j) =
  dihedral_to_complex m (sr (j - i)) :=
begin
  simp only [dihedral_to_complex],
  rw ← mul_assoc,
  rw rotation_mul_conj_lie,
  rw mul_assoc,
  rw (zmod_to_angle m).map_sub,
  rw angle_to_circle_sub,
  rw div_eq_mul_inv,
  rw mul_comm,
  rw rotation.map_mul,
end

lemma mul_3 (i j : zmod m) : dihedral_to_complex m (sr i) * dihedral_to_complex m (r j) =
  dihedral_to_complex m (sr (i + j)) :=
begin
  simp only [dihedral_to_complex],
  rw (zmod_to_angle m).map_add,
  rw angle_to_circle_add,
  rw rotation.map_mul,
  rw mul_assoc,
end

lemma mul_4 (i j : zmod m) : dihedral_to_complex m (sr i) * dihedral_to_complex m (sr j) =
  dihedral_to_complex m (r (j - i)) :=
begin
  simp only [dihedral_to_complex],
  rw ← mul_assoc,
  have : conj_lie * rotation (angle_to_circle ((zmod_to_angle m) i)) * conj_lie *
  rotation (angle_to_circle ((zmod_to_angle m) j)) = conj_lie *
  (rotation (angle_to_circle ((zmod_to_angle m) i)) * conj_lie) *
  rotation (angle_to_circle ((zmod_to_angle m) j)),
  { simp [mul_assoc], },
  rw this,
  rw rotation_mul_conj_lie,
  rw ← mul_assoc,
  rw mul_assoc,
  rw ← rotation.map_mul,
  have this₁ : ((angle_to_circle ((zmod_to_angle m) i))⁻¹ *
  angle_to_circle ((zmod_to_angle m) j)) =
  (angle_to_circle ((zmod_to_angle m) j) / angle_to_circle ((zmod_to_angle m) i)),
  { rw mul_comm,
    refl, },
  rw this₁,
  rw (zmod_to_angle m).map_sub,
  rw ← angle_to_circle_sub,
  have this₂ : conj_lie * conj_lie = 1,
  { ext1 z,
    simp[conj_lie], },
  rw this₂,
  rw one_mul,
end

variables (m)

/-- A homomorphism mapping the dihedral group to linear isometries of ℂ. -/
def dihedral_to_complex_hom: dihedral_group m →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun :=  dihedral_to_complex m,
  map_one' := begin change dihedral_to_complex m (r 0) = _, ext1 z, simp [dihedral_to_complex],
  end,
  map_mul' :=
  begin
    rintros (i | i) (j | j),
    { rw mul_1,
      refl, },
    { rw mul_2,
      refl, },
    { rw mul_3,
      refl, },
    { rw mul_4,
      refl, },
  end }
