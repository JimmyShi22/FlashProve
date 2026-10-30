-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingLight.lean: the kind "the code switch" (K2): A LIGHT
TWIN OF THE PUBLIC TEST `closingOk` (Honest/K2/Sim.lean), AND THE THEOREM THAT THE TWO SAY THE SAME.
Definitions with code; statements with their proofs.

WHY. `closingOk` asks whether the closing (`closingFor`, Honest/K2/Closing.lean) returns at zeros.
That text ends each segment's step by reckoning all that the fold leaves, at once, into arrays: as
many places as the group's code's message is long, each a sum over the group's rows. Whether the
step returns hangs on none of that. The twin walks the same refusals and folds nothing: it lays each
segment's group's rows by the closing's own text (`segmentGroupRows`, at zeros: that reads each carried
coin once and reckons no row), asks the closing's own two tests on the group, and hands on the kept
members' shapes alone. WHAT IT STILL LAYS: for each message, arrays of that message's own coins;
behind the first segment, once a segment, the list of the switch's rest (`Sizes.roomy`,
Honest/K2/Part.lean); loops over members, answers and pads. The rows stay functions that nobody
calls: no array or list of the main code's message length is made.

  `segmentLight`     one segment's step without the fold: the kept members' shapes, or the refusal
  `lightFrom`        the steps from a segment on
  `closingLightFor`  the closing's verdict at a switch: nothing, or the refusal in the closing's
                    words
  `closingOkLight`   THE LIGHT TEST, of the letters of `closingOk`
  `segmentLight_alike`, `lightFrom_alike`, `closingLight_alike`   step by step: the closing, at
                    every input, list of challenges and carried coins of the same counts, returns
                    just where the twin does, and refuses in the same words
  `closingOk_isSome`   `closingOk` is "the closing returns at zeros"
  `closingOk_light`  THE THEOREM: `closingOk table segs p = closingOkLight table segs p`
  `returnsLaw_light` the law on the closing's refusals (`returnsLaw`,
                    Honest/K2/Law/SegmentAlike.lean) with the light test as its premise

Limits. The twin's text is a second text of the closing's refusals: the theorem, not the eye, holds
the two together. How long either takes is not a matter of Lean's: no time is stated here. The light
test is shown of no place here, and neither is `closingOk`. In `returnsLaw_light` D is fixed in
front of the input w, and the right side is public only at a D that closes over no witness: Lean
would not bar a D built from one. The closing's own step `segmentLeft` (Honest/K2/Closing.lean) has
two defaults where coins are due (`R.rows.getD · zeroMessage` and `R.fresh.getD zeroMessage`), and
by its own docstring no lemma says that they are not reached; the two lemmas that it names,
`segmentRows_count` (Honest/K2/Law/GroupCount.lean) and `segmentRows_mask`
(Honest/K2/Law/RowsOfSegment.lean), speak of what `segmentGroupRows` returns, and neither is imported
here. This stands beside any sentence on what the fold leaves; the twin folds nothing and has
neither default. Nothing on what the closing leaves. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Left groupLayout zeroG)

/-- **One segment's step without the fold.** prev: the kept members' shapes that the step before
left; nothing at the first segment. k: the carried stretches. base: the number of the segment's
first. -/
def segmentLight (table : FreshTable) (S : SegmentPub) (prev : Option (List OnBytes.OracleShape))
    (k : Nat → Except String Stretch) (base : Nat) : Except String (List OnBytes.OracleShape) := do
  let codes := S.sizes.codes
  let R ← segmentGroupRows table S (prev.map fun _ => zeroLeft) (prev.getD []) (fun _ _ _ => zeroG) k
    base true
  let vars := (groupLayout codes S.sizes.code S.sizes.maskCode R.members).k
  if vars != S.foldVars || S.gamma.length != vars then
    throw "a fold has not as many challenges as its group has row variables"
  if !groupFits codes S.sizes.code S.sizes.maskCode R.members
      (((S.sent.headD #[]).back?.map (·.shape)).getD default) then
    throw "a group's shapes do not fit a fold"
  pure ((R.members.filter (·.kept)).map (·.shape))

/-- The steps from a segment on: the kept members' shapes that the last leaves; nothing where there
is no segment. -/
def lightFrom (table : FreshTable) (k : Nat → Except String Stretch) :
    List SegmentPub → (base : Nat) → Option (List OnBytes.OracleShape) →
      Except String (Option (List OnBytes.OracleShape))
  | [], _, prev => .ok prev
  | S :: rest, base, prev =>
    (segmentLight table S prev k base).bind fun W =>
      lightFrom table k rest (base + S.messages) (some W)

/-- **The closing's verdict at a switch.** next: the kept members' shapes by that switch's own
sizes. -/
def closingLightFor (table : FreshTable) (segs : List SegmentPub)
    (next : List OnBytes.OracleShape) (k : Nat → Except String Stretch) : Except String Unit :=
  (lightFrom table k segs 0 none).bind fun x =>
    match x with
    | some W =>
      if W != next then .error "a switch's kept members are not those that the fold in front left"
      else .ok ()
    | none => .error "no segment stands in front of the switch"

/-- **THE LIGHT TEST** on a place's public data. -/
def closingOkLight (table : FreshTable) (segs : List SegmentPub) (p : SwitchPlace) : Bool :=
  (closingLightFor table segs p.sizes.kept
    (Stretch.carried p.carries (shapeZerosAll p.carries))).toOption.isSome

namespace Law

/-- One segment's step. -/
theorem segmentLight_alike (table : FreshTable) (S : SegmentPub)
    (prev : Option (Left × List OnBytes.OracleShape)) (own : Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) {k k' : Nat → Except String Stretch} (hk : CoinsAlike k k')
    (base : Nat) :
    Alike (fun (a : Left × List OnBytes.OracleShape) (b : List OnBytes.OracleShape) => a.2 = b)
      (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) own heard k base)
      (segmentLight table S (prev.map (·.2)) k' base) := by
  have hγ : (challengesOr0 heard S.gamma).length = S.gamma.length := by
    simp [challengesOr0]
  have hp : (prev.map (·.1)).isSome = ((prev.map (·.2)).map fun _ => zeroLeft).isSome := by
    cases prev <;> rfl
  unfold segmentLeft segmentLight
  dsimp only
  refine Alike.bind (segmentRows_alike table S _ _ ((prev.map (·.2)).getD []) own
    (fun _ _ _ => zeroG) hp hk base true) fun R R' hR => ?_
  rw [hR, hγ]
  split
  · exact Alike.error _
  · simp only [pure_bind]
    split
    · exact Alike.error _
    · exact rfl

/-- The steps from a segment on. -/
theorem lightFrom_alike (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) {k k' : Nat → Except String Stretch} (hk : CoinsAlike k k') :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      Alike (fun (x : Option (Left × List OnBytes.OracleShape) × Nat)
          (y : Option (List OnBytes.OracleShape)) => x.1.map (·.2) = y)
        (closingFrom table own heard k segs j base prev)
        (lightFrom table k' segs base (prev.map (·.2)))
  | [], _, _, _ => rfl
  | S :: rest, j, base, prev => by
    show Alike _
      ((segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind
        fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W))
      ((segmentLight table S (prev.map (·.2)) k' base).bind fun W =>
        lightFrom table k' rest (base + S.messages) (some W))
    refine Alike.bind (segmentLight_alike table S prev (own j) heard hk base) fun W W' hW => ?_
    subst hW
    exact lightFrom_alike table own heard hk rest (j + 1) (base + S.messages) (some W)

/-- **The closing at a place returns just where the twin does, and refuses in the same words.** -/
theorem closingLight_alike (table : FreshTable) (segs : List SegmentPub)
    (next : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) {k k' : Nat → Except String Stretch} (hk : CoinsAlike k k') :
    Alike Any (closingFor table segs next own heard k) (closingLightFor table segs next k') := by
  refine Alike.bind (lightFrom_alike table own heard hk segs 0 0 none) fun x y hxy => ?_
  obtain ⟨x1, x2⟩ := x
  subst hxy
  cases x1 with
  | none => exact rfl
  | some W =>
    show Alike Any (if W.2 != next then _ else _) (if W.2 != next then _ else _)
    split
    · exact rfl
    · exact trivial

/-- `closingOk` is "the closing returns at zeros". -/
theorem closingOk_isSome (table : FreshTable) (segs : List SegmentPub) (p : SwitchPlace) :
    closingOk table segs p = (closingFor table segs p.sizes.kept (fun _ _ _ _ => zeroG) []
      (Stretch.carried p.carries (shapeZerosAll p.carries))).toOption.isSome := by
  unfold closingOk
  cases closingFor table segs p.sizes.kept (fun _ _ _ _ => zeroG) []
    (Stretch.carried p.carries (shapeZerosAll p.carries)) <;> rfl

/-- **THE THEOREM: the two tests say the same.** -/
theorem closingOk_light (table : FreshTable) (segs : List SegmentPub) (p : SwitchPlace) :
    closingOk table segs p = closingOkLight table segs p :=
  (closingOk_isSome table segs p).trans
    (Alike.isSome (closingLight_alike table segs p.sizes.kept (fun _ _ _ _ => zeroG) []
      (carriedAlike p.carries (shapeZerosAll p.carries) (shapeZerosAll p.carries))))

variable {W₀ Rc Xi Tr : Type}

/-- **The law on the closing's refusals, with the light test as its premise.** -/
theorem returnsLaw_light (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (h : closingOkLight freshTable (segs.take p.link) p = true) (w : Local W₀ Rc Xi Tr)
    (heard : List Fmt.Drawn) (ca : CsAll p.carries) :
    (lotClosingAt lay segs p (D w.x) (readers w) heard
      (Stretch.carried p.carries ca)).toOption.isSome = publicOk D lay p (segs.take p.link) w.x :=
  returnsLaw D readers lay segs p ((closingOk_light freshTable (segs.take p.link) p).trans h) w
    heard ca

end Law

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.Law.segmentLight_alike
#print axioms ProofFile.Honest.K2.Law.lightFrom_alike
#print axioms ProofFile.Honest.K2.Law.closingLight_alike
#print axioms ProofFile.Honest.K2.Law.closingOk_isSome
#print axioms ProofFile.Honest.K2.Law.closingOk_light
#print axioms ProofFile.Honest.K2.Law.returnsLaw_light
#print axioms ProofFile.Honest.K2.segmentLight
#print axioms ProofFile.Honest.K2.lightFrom
#print axioms ProofFile.Honest.K2.closingLightFor
#print axioms ProofFile.Honest.K2.closingOkLight
