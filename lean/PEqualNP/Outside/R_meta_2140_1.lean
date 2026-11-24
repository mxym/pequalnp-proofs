import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2140_1
    (hMinor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x)) 12)
    (hPrefix : ∀ (C : Circuit) (f : (Fin 9 → Bool) → Bool),
      FanInTwo C → C.size ≤ 15 →
      (¬ ∃ g ∈ C.gates[1]?.toList, 9 ∈ g.inputs) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 6)) →
      circuitFun 9 C = f →
      f (fun i => decide (i = 1)) ≠ f (fun i => decide (i = 1 ∨ i = 6)) →
      HasCircuitSize 9 f 14 ∨ HasCircuitSize 8 (fun x : Fin 8 → Bool => f ![x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3]) 12)
    (hProject : (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x)) 12) → HasCircuitSize 9 (fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x)) 14 →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧ circuitFun 8 D = (fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x)) ∧
        (D.gates.filter (fun g => !(g.op.eval [true]))).length ≤ 1 ∧
        (∀ i ∈ ([5, 6] : List ℕ),
          ∃ k j : ℕ, 8 ≤ j ∧ j < 8 + k ∧
            (∃ g, D.gates[k]? = some g ∧ g.op = GateOp.or ∧
              (g.inputs = [i,j] ∨ g.inputs = [j,i])) ∧
            ∀ t g, D.gates[t]? = some g → i ∈ g.inputs → t = k))
    (hResidue : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧ circuitFun 8 D = (fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x)) ∧
        (D.gates.filter (fun g => !(g.op.eval [true]))).length ≤ 1 ∧
        (∀ i ∈ ([5, 6] : List ℕ),
          ∃ k j : ℕ, 8 ≤ j ∧ j < 8 + k ∧
            (∃ g, D.gates[k]? = some g ∧ g.op = GateOp.or ∧
              (g.inputs = [i,j] ∨ g.inputs = [j,i])) ∧
            ∀ t g, D.gates[t]? = some g → i ∈ g.inputs → t = k)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (¬∃ x2 ∈ x1.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x2.inputs) → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hSecond hFan hFirst hCorrect
  by_contra! hSmall
  have hLe : C.size ≤ 15 := by omega
  have eF :
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = (fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x)) := by
    funext x
    exact (by decide +kernel : ∀ x : Fin 9 → Bool,
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = ((fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x))) x) x
  have eH :
      (fun x : Fin 8 → Bool => ((fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x))) ![x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3]) = (fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x)) := by
    funext x
    exact (by decide +kernel : ∀ x : Fin 8 → Bool,
      ((fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x))) ![x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3] = ((fun x : Fin 8 → Bool => (BitVec.ofNat 256 0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8).getLsbD (tableIndex x))) x) x
  have dep : ((fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x))) (fun i => decide (i = 1)) ≠
      ((fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x))) (fun i => decide (i = 1 ∨ i = 6)) := by decide +kernel
  rcases hPrefix C (fun x : Fin 9 → Bool => (BitVec.ofNat 512 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8).getLsbD (tableIndex x)) hFan hLe hSecond hFirst (hCorrect.trans eF) dep with hf | hh
  · exact hResidue (hProject hMinor hf)
  · exact hMinor (eH ▸ hh)
