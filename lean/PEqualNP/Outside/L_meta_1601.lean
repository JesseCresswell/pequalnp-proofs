import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601

lemma no_four_of_girth {V : Type} (G : SimpleGraph V)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 5 ≤ c.length) :
    ∀ a b c d : V, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  let C : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hC : C.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [SimpleGraph.Walk.isPath_def]
      simp [C, hbd, hbc.ne, hcd.ne, hda.ne, Ne.symm hac, Ne.symm hab.ne]
    · simp [C]
  have h := hgirth a C hC
  norm_num [C] at h

end PEqualNP.Outside.L_meta_1601

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hbound m H _ D hmono hcorrect hgirth hclean
  have hfour := PEqualNP.Outside.L_meta_1601.no_four_of_girth H hgirth
  have hops : ∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa using hmono g hg
  have heval : ∀ x : Fin m → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have hx := congrFun hcorrect x
    simpa [PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.MetaComplexity.NestedCover.graphFun] using hx
  have hgate : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD
        (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hop hx
    have hat : PEqualNP.MetaComplexity.NestedCover.gateAt D i = D.gates.get i := by
      exact List.getD_eq_get _ _ i
    have h := hclean i i.isLt (by rw [hat]; exact hop) x hx
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using h
  obtain ⟨S, hS, hsize⟩ := hbound m H hfour D.gates D.output hops heval hgate
  have hsize' : H.edgeFinset.card + S.card ≤ D.size + 1 := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  exact ⟨S, hS, hsize', by omega⟩
