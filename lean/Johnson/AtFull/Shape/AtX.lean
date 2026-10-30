-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/AtX.lean: A CLOSED FACT ON THE WHOLE PUBLIC RECORD, AT THE MAKERS' TWINS,
SPEAKS OF THE VERY RECORD THAT publicOfO RETURNS AT THE STORED FULL-SIZE FILES (VerifierAndGoals.storedPublicFiles).
General in the test; nothing is evaluated here.

Why. atMakers (Johnson/AtFull/Public/AtWitnesses.lean) hands a test the layers' record, the layers'
plans and the attention's plans. A test that wants the public record X whole (the table of steps
reads X at most of its cells) wants six parts more: the scan, the head's numbers, layout and plan,
the owner, the three digests. The join (publicOfO_zFull_of_rest, Johnson/AtFull/Public/Join.lean)
names them: the scan and the head's plan are written terms; the head's numbers are a term in the
scan and the layers' layout; the head's layout and the owner are what their makers return; the
digests are terms in the format's second hash function, one of them over the attention's lines, which a
third maker returns.

  xOf L G A l HLy owner: the record of these parts, field for field as in the join's conclusion.
  **atX t**: the test t at that record, the parts as their makers make them; false where a maker
    refuses. A closed Bool: no free letter. THE THREE DIGESTS STAND IN IT AS TERMS: a test that does
    not read them need not open them.
  **atX_zFull**: IF the stored layout file has 224975 bytes and atX t = true, THEN there is an X₀
    that publicOfO, at the format's second hash function, returns at VerifierAndGoals.storedPublicFiles, and t X₀ = true.
  xLazy L G A, **atXL t**, **atXL_zFull**: THE SAME WITH THE THREE FURTHER MAKERS' VALUES LAID AS
    TERMS THAT NOTHING OPENS UNLESS THE TEST READS THEM (each maker's value, or a stand-in where it
    refuses): atX asks each of the three "does it return?" before t is called, and so makes whoever
    evaluates it run the head's layout whole; atXL asks nothing more of them (atMakers itself reads
    the attention's lines: so that stand-in is never in play where atXL accepts).
  **atXH t**, **atXH_zFull**: the same with the head's layout bound by the library's withLaid
    (Johnson/AtFull/Head/PubAtFull.lean), which makes it without the tests on the calls' tables: for
    a test that reads the head's layout.

Limits. UNDER hsz, WHICH IS NOT PAID HERE (it is shown in the side library:
AtFullSide/Layout/Size.lean). At VerifierAndGoals.storedPublicFiles alone: three terms written in Ladder/Stored.lean; no
Lean code ties them to the package's folder examples/; the example's weights are synthetic. No test
is shown to accept. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Public.AtX0
import Johnson.AtFull.Head.PubAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (atMakers at_witnesses opens_yFull Makers onOk_at)
open OnBytes.Road.K4.Trial.AttK7Owners (onOk PW)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO callsDigestO)

/-- The public record of its parts, as the join's conclusion has it. -/
def xOf (L : Layer.Pub) (G : Array Layer.HPlan2) (A : Array Attention.Plan)
    (l : List Attention.Line) (HLy : Head.HL) (owner : Head.Owner) : Verify.Public :=
  { P := PW,
    digests := { hCalls := callsDigestO OnBytes.secondHashFunction "call" L.y.calls.toList,
                 hCallsA := VerifiableInference.PlanWritten.Attention.callsDigestO
                   OnBytes.secondHashFunction l,
                 hCallsH := callsDigestO OnBytes.secondHashFunction "callH" HLy.calls.toList },
    layers := L, hS := headShape PW L.y, HLy := HLy, G := G, A := A,
    H := { _root_.AtFull.Head.HW with Fp := _root_.AtFull.Head.HW.Fp.trimL }, owner := owner }

/-- **A test at the whole public record, its parts as their makers make them.** -/
def atX (t : Verify.Public → Bool) : Bool :=
  atMakers fun L G A =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk (Head.layout (headShape PW L.y) L.y.tauFC) fun HLy =>
        onOk (ownerOf L.y G) fun owner => t (xOf L G A l HLy owner)

/-- **An accept speaks of what publicOfO returns at the stored full-size files.** -/
theorem atX_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atX t = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      t X₀ = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨e3, -, -⟩, e4, ⟨e5, -⟩, e6, e7,
    e8, -, ⟨e9, -⟩, hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have h1 := at_witnesses opens_yFull M h
  have h2 := onOk_at h1 e4
  rw [ey] at h2
  have h3 := onOk_at h2 e3
  have h4 := onOk_at h3 e9
  refine ⟨_, hX, ?_⟩
  unfold xOf at h4
  rw [ey] at h4
  exact h4

/-- A maker's value, or the stand-in where it refuses. -/
def orElse {ε α : Type} (x : Except ε α) (d : α) : α :=
  match x with
  | .ok a => a
  | .error _ => d

theorem orElse_ok {ε α : Type} {x : Except ε α} {a : α} (h : x = .ok a) (d : α) :
    orElse x d = a := by
  rw [h]
  rfl

/-- The public record with the three further makers' values as terms. -/
def xLazy (L : Layer.Pub) (G : Array Layer.HPlan2) (A : Array Attention.Plan) : Verify.Public :=
  xOf L G A (orElse (Attention.readLines PW.polCallsA) [])
    (orElse (Head.layout (headShape PW L.y) L.y.tauFC) default)
    (orElse (ownerOf L.y G) ⟨{}, {}, {}, 0⟩)

/-- **A test at the whole public record; of the three further makers nothing more is asked** (the
attention's lines are read by atMakers itself). -/
def atXL (t : Verify.Public → Bool) : Bool := atMakers fun L G A => t (xLazy L G A)

/-- **An accept speaks of what publicOfO returns at the stored full-size files.** -/
theorem atXL_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXL t = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      t X₀ = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨e3, -, -⟩, e4, ⟨e5, -⟩, e6, e7,
    e8, -, ⟨e9, -⟩, hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have h1 := at_witnesses opens_yFull M h
  refine ⟨_, hX, ?_⟩
  have e4' : Attention.readLines PW.polCallsA = .ok l := e4
  have e3' : Head.layout (headShape PW yFull) yFull.tauFC = .ok HLy := e3
  unfold xLazy xOf at h1
  rw [ey, orElse_ok e4', orElse_ok e3', orElse_ok e9] at h1
  exact h1

/-- **A test at the whole public record, the head's layout by the library's own test at it**
(withLaid, Johnson/AtFull/Head/PubAtFull.lean: the layout as a record of numbers, the calls, the
forest's numbers made without the tests on the calls' tables, and the nine written counts). For a
test that reads the head's layout. -/
def atXH (t : Verify.Public → Bool) : Bool :=
  atMakers fun L G A => _root_.AtFull.Head.withLaid fun HLy =>
    t (xOf L G A (orElse (Attention.readLines PW.polCallsA) []) HLy
      (orElse (ownerOf L.y G) ⟨{}, {}, {}, 0⟩))

/-- **An accept speaks of what publicOfO returns at the stored full-size files.** -/
theorem atXH_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXH t = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      t X₀ = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨e3, -, e3L⟩, e4, ⟨e5, -⟩, e6,
    e7, e8, -, ⟨e9, -⟩, hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have h1 := at_witnesses opens_yFull M h
  obtain ⟨H', eH, h2⟩ := _root_.AtFull.Head.withLaid_true h1 _ e3L
  obtain rfl : HLy = H' := Except.ok.inj (e3.symm.trans eH)
  refine ⟨_, hX, ?_⟩
  have e4' : Attention.readLines PW.polCallsA = .ok l := e4
  unfold xOf at h2
  rw [ey, orElse_ok e4', orElse_ok e9] at h2
  exact h2

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.atX_zFull
#print axioms Johnson.AtFull.Shape.orElse_ok
#print axioms Johnson.AtFull.Shape.atXL_zFull
#print axioms Johnson.AtFull.Shape.atXH_zFull
#print axioms Johnson.AtFull.Shape.xOf
#print axioms Johnson.AtFull.Shape.atX
#print axioms Johnson.AtFull.Shape.orElse
#print axioms Johnson.AtFull.Shape.xLazy
#print axioms Johnson.AtFull.Shape.atXL
#print axioms Johnson.AtFull.Shape.atXH
