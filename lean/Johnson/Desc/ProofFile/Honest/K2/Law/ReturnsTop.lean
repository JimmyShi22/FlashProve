-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ReturnsTop.lean: the kind "the code switch" (K2): THE LAW ON
THE CLOSING's REFUSALS (`ReturnsLaw`, Honest/K2/Exact.lean), FROM ONE NAMED STEP: that the fold
which closes ONE segment returns or refuses alike at two runs. Definitions; statements with their
proofs. The law says nothing on what a run shows: it is on refusals alone.

  `CoinsAlike`      two ways to hand out carried stretches by number are alike: at each number both
                    return, stretches of one count; or both refuse, in the same words
  `SegmentAlike`    THE NAMED STEP, NOT PROVED HERE (its proof: Honest/K2/Law/SegmentAlike.lean):
                    `segmentLeft` (Honest/K2/Closing.lean) at one table, segment, list of kept
                    shapes and first number: at two runs that agree in WHETHER a fold stands in
                    front, and whose stretches are alike: at whatever is left in front, own rows and
                    challenges: both return, with the same kept shapes; or both refuse, in the same
                    words
  `closingFrom_alike`   so for the steps from a segment on: the same kept shapes and next number
  `closingFor_alike`    so for the closing at a place: it returns or refuses alike
  `carriedAlike`    the stretches of two fillings of one list of named counts are alike
  `returnsLaw_of`   `SegmentAlike` GIVES `ReturnsLaw`, at every filling, readers, layout, segments
                    and place

Limits. `SegmentAlike` is a premise here: it is proved in Honest/K2/Law/SegmentAlike.lean. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Alike
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left zeroG)

/-- Two ways to hand out carried stretches are alike. -/
def CoinsAlike (k k' : Nat → Except String Stretch) : Prop :=
  ∀ n, Alike (fun s s' : Stretch => s.due = s'.due) (k n) (k' n)

/-- **The named step.** Not proved here. -/
def SegmentAlike : Prop :=
  ∀ (table : FreshTable) (S : SegmentPub) (prev prev' : Option Left)
    (prevKept : List OnBytes.OracleShape) (own own' : Nat → Nat → Nat → Cb.Gl.E)
    (heard heard' : List Fmt.Drawn) (k k' : Nat → Except String Stretch) (base : Nat),
    prev.isSome = prev'.isSome → CoinsAlike k k' →
      Alike (fun a b : Left × List OnBytes.OracleShape => a.2 = b.2)
        (segmentLeft table S prev prevKept own heard k base)
        (segmentLeft table S prev' prevKept own' heard' k' base)

section
variable (hS : SegmentAlike) (table : FreshTable) (own own' : Nat → Nat → Nat → Nat → Cb.Gl.E)
  (heard heard' : List Fmt.Drawn) (k k' : Nat → Except String Stretch) (hk : CoinsAlike k k')
include hS hk

/-- The steps from a segment on. -/
theorem closingFrom_alike : ∀ (segs : List SegmentPub) (j base : Nat)
    (prev prev' : Option (Left × List OnBytes.OracleShape)),
    prev.map (·.2) = prev'.map (·.2) →
      Alike (fun x y : Option (Left × List OnBytes.OracleShape) × Nat =>
          x.1.map (·.2) = y.1.map (·.2) ∧ x.2 = y.2)
        (closingFrom table own heard k segs j base prev)
        (closingFrom table own' heard' k' segs j base prev')
  | [], _, _, _, _, h => ⟨h, rfl⟩
  | S :: rest, j, base, prev, prev', h => by
    have h1 : (prev.map (·.1)).isSome = (prev'.map (·.1)).isSome := by
      have := congrArg Option.isSome h
      simpa using this
    show Alike _
      ((segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind
        fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W))
      ((segmentLeft table S (prev'.map (·.1)) ((prev'.map (·.2)).getD []) (own' j) heard' k'
        base).bind
        fun W => closingFrom table own' heard' k' rest (j + 1) (base + S.messages) (some W))
    rw [h]
    exact Alike.bind (hS table S _ _ _ (own j) (own' j) heard heard' k k' base h1 hk)
      fun W W' hW => closingFrom_alike rest (j + 1) (base + S.messages) (some W) (some W')
        (congrArg some hW)

/-- The closing at a place. -/
theorem closingFor_alike (segs : List SegmentPub) (next : List OnBytes.OracleShape) :
    Alike Any (closingFor table segs next own heard k)
      (closingFor table segs next own' heard' k') := by
  refine Alike.bind
    (closingFrom_alike hS table own own' heard heard' k k' hk segs 0 0 none none rfl)
    fun x y hxy => ?_
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h1, _⟩ := hxy
  cases x1 with
  | none =>
    cases y1 with
    | none => exact rfl
    | some W' => cases h1
  | some W =>
    cases y1 with
    | none => cases h1
    | some W' =>
      have h2 : W.2 = W'.2 := Option.some.inj h1
      show Alike Any (if W.2 != next then _ else _) (if W'.2 != next then _ else _)
      rw [h2]
      split
      · exact rfl
      · exact trivial

end

/-- The stretches of two fillings of one list of named counts. -/
theorem carriedAlike (ds : List (String × Due)) (c c' : CsAll ds) :
    CoinsAlike (Stretch.carried ds c) (Stretch.carried ds c') :=
  fun n => carried_alike ds c c' n

variable {W₀ Rc Xi Tr : Type}

/-- **The named step gives the law.** -/
theorem returnsLaw_of (hS : SegmentAlike) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List SegmentPub) (p : SwitchPlace) : ReturnsLaw D readers lay segs p := by
  intro hok w heard ca
  unfold lotClosingAt publicOk
  cases hl : ownLaid (D w.x) lay p (segs.take p.link) with
  | error e => rfl
  | ok u =>
    have h1 : (closingFor freshTable (segs.take p.link) p.sizes.kept (fun _ _ _ _ => zeroG) []
        (Stretch.carried p.carries (shapeZerosAll p.carries))).toOption.isSome = true := by
      unfold closingOk at hok
      cases hc : closingFor freshTable (segs.take p.link) p.sizes.kept (fun _ _ _ _ => zeroG) []
          (Stretch.carried p.carries (shapeZerosAll p.carries)) with
      | error e => rw [hc] at hok; cases hok
      | ok W => rfl
    exact (Alike.isSome (closingFor_alike hS freshTable _ (fun _ _ _ _ => zeroG) heard []
      (Stretch.carried p.carries ca) (Stretch.carried p.carries (shapeZerosAll p.carries))
      (carriedAlike p.carries ca (shapeZerosAll p.carries)) (segs.take p.link)
      p.sizes.kept)).trans h1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.CoinsAlike
#print axioms ProofFile.Honest.K2.Law.SegmentAlike
#print axioms ProofFile.Honest.K2.Law.closingFrom_alike
#print axioms ProofFile.Honest.K2.Law.closingFor_alike
#print axioms ProofFile.Honest.K2.Law.carriedAlike
#print axioms ProofFile.Honest.K2.Law.returnsLaw_of
