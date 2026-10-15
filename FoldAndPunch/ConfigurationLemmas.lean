import FoldAndPunch.Folding
import FoldAndPunch.FoldLemmas

/-! Consistency of flat states and the idealized all-layer fold operation. -/

noncomputable section
namespace FoldAndPunch

/-- An unfolded subset of the sheet has exactly one layer at each surviving point. -/
theorem flatConfiguration_wellFormed {n : ℕ} (P : Paper n) (material : Set Point)
    (inside : material ⊆ P.region) : (flatConfiguration material).WellFormed P := by
  classical
  refine ⟨inside, ?_, ?_⟩
  · intro q
    by_cases present : q ∈ material <;> simp [flatConfiguration, present]
  · intro q x
    by_cases present : q ∈ material
    · simp only [flatConfiguration, ite_eq_left present, List.mem_singleton, id_eq]
      constructor
      · intro same
        exact ⟨same ▸ present, same⟩
      · intro located
        exact located.2
    · simp only [flatConfiguration, ite_eq_right present, List.not_mem_nil, id_eq,
        false_iff, not_and]
      intro materialPoint same
      apply present
      rw [← same]
      exact materialPoint

/-- All-layer folding preserves the correspondence between locations and stacks.
This proves consistency of the idealized fold definition, not a 3D motion claim. -/
theorem Configuration.fold_wellFormed {n : ℕ} {P : Paper n} {C : Configuration}
    (wellFormed : C.WellFormed P) (f : Fold) : (C.fold f).WellFormed P := by
  classical
  obtain ⟨inside, noDuplicates, stackMembership⟩ := wellFormed
  refine ⟨inside, ?_, ?_⟩
  · intro q
    by_cases moving : f.moving q
    · simp [Configuration.fold, moving]
    · by_cases onAxis : q ∈ f.axis
      · simpa [Configuration.fold, moving, onAxis] using noDuplicates q
      · -- Off the axis, reflected and stationary stacks have no label in common.
        have disjoint : List.Disjoint (C.stack (f.reflect q)).reverse (C.stack q) := by
          apply List.disjoint_left.mpr
          intro x reflected stationary
          have reflectedPosition :=
            ((stackMembership (f.reflect q) x).1 (List.mem_reverse.mp reflected)).2
          have stationaryPosition := ((stackMembership q x).1 stationary).2
          have fixed : f.reflect q = q := reflectedPosition.symm.trans stationaryPosition
          exact onAxis ((f.reflect_fixed_iff q).1 fixed)
        have reflectedNodup := List.nodup_reverse.mpr (noDuplicates (f.reflect q))
        have stationaryNodup := noDuplicates q
        cases placement : f.placement with
        | top =>
          simpa [Configuration.fold, moving, onAxis, placement, placeStack] using
            (reflectedNodup.append stationaryNodup disjoint)
        | bottom =>
          simpa [Configuration.fold, moving, onAxis, placement, placeStack] using
            (stationaryNodup.append reflectedNodup disjoint.symm)
  · intro q x
    by_cases moving : f.moving q
    · -- The vacated half-plane has neither a stack nor any geometric preimages.
      simp only [Configuration.fold, ite_eq_left moving, List.not_mem_nil,
        false_iff, not_and]
      intro _ mapped
      have stationary := f.pointMap_not_moving (C.position x)
      rw [mapped] at stationary
      exact stationary moving
    · by_cases onAxis : q ∈ f.axis
      · simp only [Configuration.fold, ite_eq_right moving, ite_eq_left onAxis]
        rw [stackMembership, f.pointMap_eq_on_axis onAxis]
      · -- On the receiving side, membership is exactly membership in either stack.
        simp only [Configuration.fold, ite_eq_right moving, ite_eq_right onAxis]
        rw [f.pointMap_eq_off_axis moving onAxis]
        cases f.placement <;>
          simp [placeStack, stackMembership, and_or_left, or_comm]

/-- The initial, unpunched polygon is a well-formed configuration. -/
theorem Paper.initial_wellFormed {n : ℕ} (P : Paper n) : P.initial.WellFormed P := by
  apply flatConfiguration_wellFormed
  exact Set.Subset.rfl

end FoldAndPunch
