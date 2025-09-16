import Mathlib.Order.FixedPoints

open Set
open scoped Classical

variable {α : Type _}

namespace Tarski

section

variable [CompleteLattice α]

/-- The least fixed point of a self-map `f`. -/
def lfp (f : α → α) : α := sInf {x : α | f x ≤ x}

/-- The greatest fixed point of a self-map `f`. -/
def gfp (f : α → α) : α := sSup {x : α | x ≤ f x}

lemma lfp_le_of_mem {f : α → α} {x : α} (hx : f x ≤ x) : lfp f ≤ x := by
  have hx' : x ∈ {x : α | f x ≤ x} := hx
  simpa [lfp] using sInf_le hx'

lemma le_of_mem_gfp {f : α → α} {x : α} (hx : x ≤ f x) : x ≤ gfp f := by
  have hx' : x ∈ {x : α | x ≤ f x} := hx
  simpa [gfp] using le_sSup hx'

lemma lfp_le_flfp {f : α → α} (hf : Monotone f) : f (lfp f) ≤ lfp f := by
  refine le_sInf ?_
  intro x hx
  have hx' : f x ≤ x := hx
  have hμ_le : lfp f ≤ x := lfp_le_of_mem (f := f) hx
  exact (hf hμ_le).trans hx'

lemma lfp_le_f {f : α → α} (hf : Monotone f) : lfp f ≤ f (lfp f) := by
  have hx : f (lfp f) ≤ lfp f := lfp_le_flfp (f := f) hf
  have hx_mem : f (lfp f) ∈ {x : α | f x ≤ x} := by
    show f (f (lfp f)) ≤ f (lfp f)
    exact hf hx
  simpa [lfp] using sInf_le hx_mem

lemma lfp_eq {f : α → α} (hf : Monotone f) : f (lfp f) = lfp f :=
  le_antisymm (lfp_le_flfp (f := f) hf) (lfp_le_f (f := f) hf)

lemma gfp_le {f : α → α} (hf : Monotone f) : gfp f ≤ f (gfp f) := by
  refine sSup_le ?_
  intro x hx
  have hx' : x ≤ f x := hx
  have hx_le : x ≤ gfp f := le_of_mem_gfp (f := f) hx
  have : f x ≤ f (gfp f) := hf hx_le
  exact hx'.trans this

lemma fgfp_le {f : α → α} (hf : Monotone f) : f (gfp f) ≤ gfp f := by
  have hx : f (gfp f) ∈ {x : α | x ≤ f x} := by
    show f (gfp f) ≤ f (f (gfp f))
    exact hf (gfp_le (f := f) hf)
  simpa [gfp] using le_sSup hx

lemma gfp_eq {f : α → α} (hf : Monotone f) : f (gfp f) = gfp f :=
  le_antisymm (fgfp_le (f := f) hf) (gfp_le (f := f) hf)

lemma lfp_isLeast {f : α → α} (hf : Monotone f) :
    IsLeast {x : α | f x = x} (lfp f) := by
  refine ⟨?_, ?_⟩
  · exact lfp_eq (f := f) hf
  · intro x hx
    have hx' := hx
    simp [Set.mem_setOf_eq] at hx'
    have hx_mem : f x ≤ x := by
      calc
        f x = x := hx'
        _ ≤ x := le_rfl
    exact lfp_le_of_mem (f := f) hx_mem

lemma gfp_isGreatest {f : α → α} (hf : Monotone f) :
    IsGreatest {x : α | f x = x} (gfp f) := by
  refine ⟨?_, ?_⟩
  · exact gfp_eq (f := f) hf
  · intro x hx
    have hx' := hx
    simp [Set.mem_setOf_eq] at hx'
    have hx_mem : x ≤ f x := by
      calc
        x = f x := hx'.symm
        _ ≤ f x := le_rfl
    exact le_of_mem_gfp (f := f) hx_mem

/-- Tarski's fixed point theorem: a monotone self-map on a complete lattice has
least and greatest fixed points. -/
lemma tarski {f : α → α} (hf : Monotone f) :
    ∃ μ ν, IsLeast {x : α | f x = x} μ ∧ IsGreatest {x : α | f x = x} ν := by
  refine ⟨lfp f, gfp f, lfp_isLeast (f := f) hf, gfp_isGreatest (f := f) hf⟩

end

end Tarski
