-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruStops.lean: what the record of the honest side reads of a prover
beside runC, at a prover read through (Honest/ThruRun.lean): its stops and the state of a run before
a part.

  stop0B_thru, badB_thru, hidB_thru   the three sets of challenges of the record
  halved_thru, halvedAll_thru, rooted_thru, rootedAll_thru   two tests on the sides' places
  midInW_thru          the state before an address, read through
  sharedMid_thru, midAtW_thru   the state of a run before a part: the same error, or the state
                       as the prover's side reads it

By what. chainStopAt_thru, walk_of_thru, ChainProgress.start_of_narrow, ready_thru (Honest/ThruRun.lean).

Limits.
  * Mid.narrow keeps all but the input's type: a law on the state at the base prover carries to the
    state at the prover read through by Mid.narrow alone.
  * The strategies requestStrategyTrackingVerifier and sharedPartStrategyTrackingVerifier are not treated: where runC errs they still send.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruRun
import Johnson.Desc.ProofFile.Honest.Record
import Johnson.Desc.ProofFile.Honest.MidW
import Johnson.Desc.ProofFile.Honest.Law.PlanGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

variable {S Cl Xi V V' W W' Y W₀ W₀' Rc Rc' Ky Tr X₀ X : Type}

/-! ## 1 The stops of the record -/

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X)

/-- The shared chain's stop of the prover read through. -/
theorem stop0B_thru (ds : List Fmt.Drawn) : stop0B F (H.thru g rd d) ds = stop0B F H ds :=
  congrArg Option.isSome
    (chainStopAt_thru id (Common.thru (Ky := Ky) g rd) none none rfl F.shared.blocksInOrder H.shared [] ds)

/-- Its first stops. -/
theorem badB_thru (ds : List Fmt.Drawn × List Fmt.Drawn) :
    badB F (H.thru g rd d) ds = badB F H ds :=
  congrArg₂ (fun a b : Option Why => a.isSome || b.isSome)
    (chainStopAt_thru (Local.thru g rd) (Local.thru g rd) none none rfl F.first.blocksInOrder H.first [] ds.1)
    (chainStopAt_thru (Local.thru g rd) (Local.thru g rd) none none rfl F.second.blocksInOrder H.second ds.1
      ds.2)

/-- Its second stops. -/
theorem hidB_thru (w : W₀') (rc : Rc') (x : Xi) (ds : List Fmt.Drawn × List Fmt.Drawn) :
    hidB F (H.thru g rd d) w rc x ds = hidB F H (g w) (rd rc) x ds := by
  have e : (H.thru g rd d).trace w x = H.trace (g w) x := rfl
  unfold hidB
  rw [e]
  cases H.trace (g w) x with
  | none => rfl
  | some tr =>
    exact congrArg₂ (fun a b : Option Why => (a == some .hid) || (b == some .hid))
      (chainStopAt_thru (Local.thru g rd) (Local.thru g rd)
        (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
        (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.first.blocksInOrder H.first [] ds.1)
      (chainStopAt_thru (Local.thru g rd) (Local.thru g rd)
        (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
        (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.second.blocksInOrder H.second ds.1 ds.2)

end

/-! ## 2 Two tests on places -/

/-- A test on places does not see a side read through. -/
theorem any_place_thru (see : V' → V) (wit : W' → W) (hs : List (Placed V W Y))
    (a : VerifiableInference.Desc.Place) :
    (hs.map (Placed.thru see wit)).any (fun h => h.place == a) = hs.any fun h => h.place == a := by
  rw [List.any_map]
  rfl

/-- The test that a side stands wherever an item is declared. -/
theorem halved_thru (see : V' → V) (wit : W' → W) (bs : List (Block S Cl))
    (hs : List (Placed V W Y)) : halved bs (hs.map (Placed.thru see wit)) = halved bs hs := by
  unfold halved
  simp only [any_place_thru]

/-- The test that a side stands wherever a root is sent. -/
theorem rooted_thru (see : V' → V) (wit : W' → W) (bs : List (Block S Cl))
    (hs : List (Placed V W Y)) : rooted bs (hs.map (Placed.thru see wit)) = rooted bs hs := by
  unfold rooted
  simp only [any_place_thru]

/-- The first at the three chains. -/
theorem halvedAll_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : halvedAll F (H.thru g rd d) = halvedAll F H := by
  have h₁ : halved F.first.blocksInOrder (H.thru g rd d).first = halved F.first.blocksInOrder H.first :=
    halved_thru _ _ _ _
  have h₂ : halved F.shared.blocksInOrder (H.thru g rd d).shared = halved F.shared.blocksInOrder H.shared :=
    halved_thru _ _ _ _
  have h₃ : halved F.second.blocksInOrder (H.thru g rd d).second = halved F.second.blocksInOrder H.second :=
    halved_thru _ _ _ _
  unfold halvedAll
  rw [h₁, h₂, h₃]

/-- The second at the three chains. -/
theorem rootedAll_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : rootedAll F (H.thru g rd d) = rootedAll F H := by
  have h₁ : rooted F.first.blocksInOrder (H.thru g rd d).first = rooted F.first.blocksInOrder H.first :=
    rooted_thru _ _ _ _
  have h₂ : rooted F.shared.blocksInOrder (H.thru g rd d).shared = rooted F.shared.blocksInOrder H.shared :=
    rooted_thru _ _ _ _
  have h₃ : rooted F.second.blocksInOrder (H.thru g rd d).second = rooted F.second.blocksInOrder H.second :=
    rooted_thru _ _ _ _
  unfold rootedAll
  rw [h₁, h₂, h₃]

/-! ## 3 The state of a run before a part -/

/-- A result read by n, behind which a second map stands. -/
theorem map_bind_when_read {ε α β γ γ' : Type} {e' : Except ε α} {e : Except ε β} (n : α → β)
    (h : e'.map n = e) (M : γ → γ') {k' : α → Except ε γ} {k : β → Except ε γ'}
    (hk : ∀ a, Except.map M (k' a) = k (n a)) :
    Except.map M (e'.bind k') = e.bind k := by
  subst h
  cases e' with
  | error x => rfl
  | ok a => exact hk a

/-- **The state before an address, read through.** -/
theorem midInW_thru (wit : W' → W) (L : Lay) (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z : ChainProgress S Cl W' Y) (a : Addr) :
    (midInW L (ss.map (Step.thru wit)) ds z a).map (Option.map (Mid.narrow wit)) =
      midInW L ss ds (ChainProgress.narrow wit z) a := by
  have h1 : (ss.map (Step.thru wit)).any (·.addr == a) = ss.any (·.addr == a) := by
    rw [List.any_map]
    rfl
  have h2 : ((ss.map (Step.thru wit)).takeWhile fun s => s.addr != a).length =
      (ss.takeWhile fun s => s.addr != a).length := by
    rw [List.takeWhile_map, List.length_map]
    rfl
  have h3 : (ss.map (Step.thru wit)).take (ss.takeWhile fun s => s.addr != a).length =
      (ss.take (ss.takeWhile fun s => s.addr != a).length).map (Step.thru wit) := by
    rw [List.map_take]
  have hw := walk_of_thru wit L h3 (ds.take (ss.takeWhile fun s => s.addr != a).length) z
  unfold midInW
  dsimp only
  rw [h1, h2]
  cases hc : ss.any (·.addr == a) with
  | false => rfl
  | true =>
    show Except.map (Option.map (Mid.narrow wit)) (Except.map (·.mid)
        (walk L ((ss.map (Step.thru wit)).take (ss.takeWhile fun s => s.addr != a).length)
          (ds.take (ss.takeWhile fun s => s.addr != a).length) z)) =
      Except.map (·.mid) (walk L (ss.take (ss.takeWhile fun s => s.addr != a).length)
        (ds.take (ss.takeWhile fun s => s.addr != a).length) (ChainProgress.narrow wit z))
    rw [← hw]
    cases walk L ((ss.map (Step.thru wit)).take (ss.takeWhile fun s => s.addr != a).length)
      (ds.take (ss.takeWhile fun s => s.addr != a).length) z with
    | error e => rfl
    | ok z' => rfl

/-- What midSharedAtW does behind ready. -/
def midSharedFrom (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (stored : Nat → Nat → Option (List UInt64)) (x : Xi) (ρ : Draws) (a : Addr)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Except Refusal (Option (Mid (Common W₀ Rc Ky) X₀)) :=
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  midInW ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂ a

/-- What midAtW does behind ready. -/
def midFrom (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (stored : Nat → Nat → Option (List UInt64)) (x : Xi) (ρ : Draws) (a : Addr)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Except Refusal (Option (Mid (Local W₀ Rc Xi Tr) X)) :=
  (ChainProgress.start ⟨0, 0, stored, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
    (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
  if R.first.any (·.addr == a) then midInW ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁ a else
  (walk ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁).bind fun z₁ =>
  if !sealQuiet z₁.laid then .error ⟨.unfit, "the sealing round sends or draws something"⟩ else
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  (walk ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂).bind fun z₂ =>
  (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
    (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
    (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).bind fun a₃ =>
  midInW ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩ R.second ρ.second a₃ a

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)
  (a : Addr)

/-- Behind ready, the shared chain. -/
theorem midSharedFrom_thru (stored : Nat → Nat → Option (List UInt64))
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) :
    (midSharedFrom F (H.thru g rd d) stored x ρ a R').map
        (Option.map (Mid.narrow (Common.thru g rd))) =
      midSharedFrom F H stored x ρ a R := by
  unfold midSharedFrom
  refine map_bind_when_read (ChainProgress.narrow (Common.thru g rd))
    (ChainProgress.start_of_narrow (m' := some (R'.start₂ (H.thru g rd d))) _ _ _
      (congrArg some (Ready.start₂_narrow g rd d H h)) _ _) _ fun a₂ => ?_
  rw [h.shared]
  exact midInW_thru _ _ _ _ _ _

/-- **The state before a part of the shared chain, read through.** -/
theorem sharedMid_thru (hd : H.inRange (g d) = H.inRange H.dummy) :
    (midSharedAtW F B (H.thru g rd d) w rc x c ρ a).map
        (Option.map (Mid.narrow (Common.thru g rd))) =
      midSharedAtW F B H (g w) (rd rc) x c ρ a := by
  have e₁ : midSharedAtW F B (H.thru g rd d) w rc x c ρ a =
      (ready F B (H.thru g rd d) w rc x c).bind
        (midSharedFrom F (H.thru g rd d) (H.storedWords (g w) (rd rc)) x ρ a) := rfl
  have e₂ : midSharedAtW F B H (g w) (rd rc) x c ρ a =
      (ready F B H (g w) (rd rc) x c).bind
        (midSharedFrom F H (H.storedWords (g w) (rd rc)) x ρ a) := rfl
  rw [e₁, e₂, ready_thru g rd d F B H w rc x c hd]
  cases hR : ready F B H (g w) (rd rc) x c with
  | error e => rfl
  | ok R =>
    exact midSharedFrom_thru g rd d F H x ρ a _ (Ready.reads_thru g rd hR)

/-- Behind ready, the first and the second chain. -/
theorem midFrom_thru (stored : Nat → Nat → Option (List UInt64))
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) :
    (midFrom F (H.thru g rd d) stored x ρ a R').map (Option.map (Mid.narrow (Local.thru g rd))) =
      midFrom F H stored x ρ a R := by
  unfold midFrom
  refine map_bind_when_read (ChainProgress.narrow (Local.thru g rd))
    (ChainProgress.start_of_narrow (m' := some (R'.start₁ (H.thru g rd d))) _ _ _
      (congrArg some (Ready.start₁_narrow g rd d H h)) _ _) _ fun a₁ => ?_
  have hany : R'.first.any (·.addr == a) = R.first.any (·.addr == a) := by
    rw [h.first, List.any_map]
    rfl
  rw [hany]
  by_cases hq : R.first.any (·.addr == a) = true
  · rw [if_pos hq]
    refine Eq.trans ?_ (if_pos hq).symm
    rw [h.first]
    exact midInW_thru _ _ _ _ _ _
  · rw [if_neg hq]
    refine Eq.trans ?_ (if_neg hq).symm
    refine map_bind_when_read (ChainProgress.narrow (Local.thru g rd)) (walk_of_thru _ _ h.first _ _) _
      fun z₁ => ?_
    by_cases hs : (!sealQuiet z₁.laid) = true
    · rw [if_pos hs]
      exact (if_pos hs).symm
    · rw [if_neg hs]
      refine Eq.trans ?_ (if_neg hs).symm
      refine map_bind_when_read (ChainProgress.narrow (Common.thru g rd))
        (ChainProgress.start_of_narrow (m' := some (R'.start₂ (H.thru g rd d))) _ _ _
          (congrArg some (Ready.start₂_narrow g rd d H h)) _ _) _ fun a₂ => ?_
      refine map_bind_when_read (ChainProgress.narrow (Common.thru g rd)) (walk_of_thru _ _ h.shared _ _) _
        fun z₂ => ?_
      refine map_bind_when_read (ChainProgress.narrow (Local.thru g rd))
        (ChainProgress.start_of_narrow _ _ _ (meet_read g rd d H h z₁.mid z₂.mid) _ _) _ fun a₃ => ?_
      rw [h.second]
      exact midInW_thru _ _ _ _ _ _

/-- **The state before a part of the first or the second chain, read through.** -/
theorem midAtW_thru (hd : H.inRange (g d) = H.inRange H.dummy) :
    (midAtW F B (H.thru g rd d) w rc x c ρ a).map (Option.map (Mid.narrow (Local.thru g rd))) =
      midAtW F B H (g w) (rd rc) x c ρ a := by
  have e₁ : midAtW F B (H.thru g rd d) w rc x c ρ a =
      (ready F B (H.thru g rd d) w rc x c).bind
        (midFrom F (H.thru g rd d) (H.storedWords (g w) (rd rc)) x ρ a) := rfl
  have e₂ : midAtW F B H (g w) (rd rc) x c ρ a =
      (ready F B H (g w) (rd rc) x c).bind
        (midFrom F H (H.storedWords (g w) (rd rc)) x ρ a) := rfl
  rw [e₁, e₂, ready_thru g rd d F B H w rc x c hd]
  cases hR : ready F B H (g w) (rd rc) x c with
  | error e => rfl
  | ok R =>
    exact midFrom_thru g rd d F H x ρ a _ (Ready.reads_thru g rd hR)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stop0B_thru
#print axioms ProofFile.Honest.badB_thru
#print axioms ProofFile.Honest.hidB_thru
#print axioms ProofFile.Honest.any_place_thru
#print axioms ProofFile.Honest.halved_thru
#print axioms ProofFile.Honest.rooted_thru
#print axioms ProofFile.Honest.halvedAll_thru
#print axioms ProofFile.Honest.rootedAll_thru
#print axioms ProofFile.Honest.map_bind_when_read
#print axioms ProofFile.Honest.midInW_thru
#print axioms ProofFile.Honest.midSharedFrom
#print axioms ProofFile.Honest.midFrom
#print axioms ProofFile.Honest.midSharedFrom_thru
#print axioms ProofFile.Honest.sharedMid_thru
#print axioms ProofFile.Honest.midFrom_thru
#print axioms ProofFile.Honest.midAtW_thru
