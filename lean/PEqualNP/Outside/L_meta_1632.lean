import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

lemma other_point_not_on_line {N : ℕ} (L : Fin N → Finset (Fin N))
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (l l' x p : Fin N) (hne : l ≠ l')
    (hx : x ∈ L l) (hx' : x ∈ L l')
    (hp : p ∈ L l) (hpx : p ≠ x) : p ∉ L l' := by
  intro hp'
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hinter l l' hne)
  have hxc : x = c := by
    simpa [hc] using (Finset.mem_inter.mpr ⟨hx, hx'⟩ : x ∈ L l ∩ L l')
  have hpc : p = c := by
    simpa [hc] using (Finset.mem_inter.mpr ⟨hp, hp'⟩ : p ∈ L l ∩ L l')
  exact hpx (hpc.trans hxc.symm)

lemma fold_input (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false
      = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

end PEqualNP.Outside.L_meta_1632

theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  intro q N L i0 p0 p1 _hq _hN _hcard hinter _hjoin _h01 _h0 _h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hp0
    exact ⟨hl'.2, PEqualNP.Outside.L_meta_1632.other_point_not_on_line L hinter l l' p0 p hne hl.1 hl'.1 hp hp0⟩
  · intro m m' hm hm' hne p hp hp1
    exact ⟨hm'.2, PEqualNP.Outside.L_meta_1632.other_point_not_on_line L hinter m m' p1 p hne hm.1 hm'.1 hp hp1⟩
  · intro m hm
    exact hm.2
  · intro l hl
    exact hl.2
  · intro M m _hM hm p _hp hpm
    exact ⟨hm.2, hpm⟩
  · intro l m hl hm
    apply Finset.card_eq_one.mp
    apply hinter l m
    intro heq
    exact hm.2 (heq ▸ hl.1)
  · intro gates _hops _hnonempty _hprior p t
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [PEqualNP.Outside.L_meta_1632.fold_input gates _ _ (by simp)]
    rw [List.getD_eq_getElem _ false (by simp)]
    simp
