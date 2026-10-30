-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK10.lean: the closing of a segment (K10), as a member that stands in front of
a later closing: its block at the first chain's state (`K9.closing`, Johnson/Desc/First/Batch/Place.lean) behaves alike
at two states that are equal once wiped. Five definitions with code; the rest are theorems.

Words. The wiped state (`wipeS`, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile `out.pending`, and the claim at the chain's end) keep theirs. The wipings of parts named
there and in Wipe/WipeLaws.lean do the like to a part of a state.

What is proved. `closing_whole2`: `Whole2 wipeS (K9.closing P)` (Wipe/Alike.lean). On the way, each in the form "at the
wiped arguments and at the arguments: the same refusal, or values that are equal once wiped":
  `foldShapeFits_wipe`, `foldMaskFits_wipe`, `foldRowFits_rel`   the fold's three tests read no target
  `foldOutput_rel`   what a fold returns depends on the running claim in its target alone
  `rounds_blind`     the fold's rounds return the same list of challenges at any two running claims
  `foldD_wiped`, `fold_wiped`, `fold_rel`   the fold, where the fresh mask came in an earlier message
  `bat_alike`, `closing_wiped`, `closeFrame_wiped`   the batching, the closing of a link, the frame's closing
  `recOf_wipe`, `putRec_wipe`, `closing_wiped_at`   K10's part of the state, and the block's decision

By what. The texts of Johnson/Desc/First/Close/Closing.lean are unfolded and followed bind by bind. The batched row's
target goes into the first running claim, each running claim into the next, and the last into the target of the rows
that the frame keeps. That target is set to zero on both sides before they are compared, so no arithmetic on a claim is
done. Since the block writes a target, its value at the wiped state is not its value wiped; the two are equal once both
are wiped (`Decides2.of_wiped`).

Limits. The fold's arm in which the fresh mask's root comes in the fold's own first message is not treated: the closing
of a link does not take it. The laws hold at all states and rounds, whether a run can reach them or not. No property of
the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeGround
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement GroupRow GroupLayout SingleRows ReqFrame FoldShape foldOutput)
open Desc.Plain (DState)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.Own (foldShapeFits foldMaskFits foldRowFits)
open VerifiableInference.Desc.Ground (spendAsMaskL spendAsMaskP)
open VerifiableInference.Desc.First.Close (Par Rec Plan need got bat rounds foldD fold closing closeFrame entries onSt)

/-! ## 1 General laws -/

/-- Two binds are equal after a map where their heads are equal after a map φ and their tails are equal after the
map at values that φ makes equal. -/
theorem ebind_rel {ε β γ δ ζ : Type} {ψ ψ' : γ → δ} (φ : β → ζ) {p p' : Except ε β} {k k' : β → Except ε γ}
    (hp : p.map φ = p'.map φ) (h : ∀ b b', φ b = φ b' → (k b).map ψ = (k' b').map ψ') :
    (p >>= k).map ψ = (p' >>= k').map ψ' := by
  cases p with
  | error a =>
    cases p' with
    | error a' =>
      have e : a = a' := Except.error.inj hp
      subst e
      rfl
    | ok b' => cases hp
  | ok b =>
    cases p' with
    | error a' => cases hp
    | ok b' => exact h b b' (Except.ok.inj hp)

/-- Two maps of outcomes are equal where the outcomes are equal after a map φ and the two functions agree at values
that φ makes equal. -/
theorem emap_rel {ε β δ ζ : Type} (φ : β → ζ) {p p' : Except ε β} {g g' : β → δ} (hp : p.map φ = p'.map φ)
    (h : ∀ b b', φ b = φ b' → g b = g' b') : p.map g = p'.map g' := by
  cases p with
  | error a =>
    cases p' with
    | error a' =>
      have e : a = a' := Except.error.inj hp
      subst e
      rfl
    | ok b' => cases hp
  | ok b =>
    cases p' with
    | error a' => cases hp
    | ok b' => exact congrArg (fun t => (Except.ok t : Except ε δ)) (h b b' (Except.ok.inj hp))

/-- `List.all` is the same at two tests that agree at each entry. -/
theorem all_same {α : Type} (l : List α) {p q : α → Bool} (h : ∀ a, p a = q a) : l.all p = l.all q := by
  rw [funext h]

/-- `List.any` is the same at two tests that agree at each entry. -/
theorem any_same {α : Type} (l : List α) {p q : α → Bool} (h : ∀ a, p a = q a) : l.any p = l.any q := by
  rw [funext h]

/-! ## 2 The fold's three tests and its output -/

/-- Whether a fold's shape fits is the same at a statement and at that statement wiped. -/
theorem foldShapeFits_wipe (S : Statement) (F : FoldShape) : foldShapeFits (wipeSt S) F = foldShapeFits S F := by
  unfold VerifiableInference.Desc.Own.foldShapeFits
  rw [wipeSt_codes]
  cases S.codes.base[F.code]? with
  | none => cases S.codes.mask[F.maskCode]? <;> rfl
  | some c =>
    cases S.codes.mask[F.maskCode]? with
    | none => rfl
    | some zk =>
      dsimp only
      refine congrArg₂ and (congrArg₂ and rfl (all_same _ fun i => ?_)) (any_same _ fun i => ?_)
      · rw [wipeSt_oracle_at]
        cases S.oracles[F.layout.members.getD i OnBytes.noId]? <;> rfl
      · rw [wipeSt_oracle_at]
        cases S.oracles[F.layout.members.getD i OnBytes.noId]? <;> rfl

/-- Whether a message can be a fold's fresh mask is the same at a statement and at that statement wiped. -/
theorem foldMaskFits_wipe (S : Statement) (F : FoldShape) (fresh : Nat) :
    foldMaskFits (wipeSt S) F fresh = foldMaskFits S F fresh := by
  unfold VerifiableInference.Desc.Own.foldMaskFits
  rw [wipeSt_oracle_at]
  cases S.oracles[fresh]? <;> rfl

/-- Whether a row has the sizes of the group's tables is the same at a statement and at that statement wiped, and at
two rows that differ in their targets alone. -/
theorem foldRowFits_rel (S : Statement) (F : FoldShape) {row row' : GroupRow} (h : wipeG row' = wipeG row) :
    foldRowFits (wipeSt S) F row' = foldRowFits S F row := by
  have hc : row'.c = row.c := (congrArg (fun r : GroupRow => r.c) h :)
  have hd : row'.d = row.d := (congrArg (fun r : GroupRow => r.d) h :)
  have hk : row'.kept = row.kept := (congrArg (fun r : GroupRow => r.kept) h :)
  unfold VerifiableInference.Desc.Own.foldRowFits
  rw [tableBits_wipe, wipeSt_codes, hc, hd, hk]

/-- What a fold returns, with its target set to zero, is the same at a statement and at that statement wiped, at two
rows that differ in their targets alone, and at any two running claims. -/
theorem foldOutput_rel (S : Statement) (F : FoldShape) {row row' : GroupRow} (h : wipeG row' = wipeG row) (fr : Nat)
    (eps : E) (γ : List E) (c c' : E) :
    singleRowsWithZeroTarget (foldOutput (wipeSt S) F row' fr eps γ c) = singleRowsWithZeroTarget (foldOutput S F row fr eps γ c') := by
  have hc : row'.c = row.c := (congrArg (fun r : GroupRow => r.c) h :)
  have hd : row'.d = row.d := (congrArg (fun r : GroupRow => r.d) h :)
  have hk : row'.kept = row.kept := (congrArg (fun r : GroupRow => r.kept) h :)
  unfold singleRowsWithZeroTarget OnBytes.foldOutput
  simp only [mainRows_at_wipe, wipeSt_codes, hc, hd, hk]

/-! ## 3 The fold's rounds: the challenges do not hang on the running claim -/

/-- Two outcomes that hold the same list of challenges still do once one more challenge is put in front of each
list. -/
theorem rounds_step {x x' : Except String (List E × E)} (g : E) (h : x.map (·.1) = x'.map (·.1)) :
    (x >>= fun y => (pure (g :: y.1, y.2) : Except String (List E × E))).map (·.1) =
      (x' >>= fun y => (pure (g :: y.1, y.2) : Except String (List E × E))).map (·.1) :=
  ebind_rel (fun y : List E × E => y.1) h fun _ _ hb =>
    congrArg (fun l : List E => (Except.ok (g :: l) : Except String (List E))) hb

/-- **The fold's rounds**, at any two running claims: the same refusal, or the same list of challenges. -/
theorem rounds_blind : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (c c' : E),
    (rounds es rs c).map (·.1) = (rounds es rs c').map (·.1)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | e :: es, r :: rs, c, c' => by
    unfold VerifiableInference.Desc.First.Close.rounds
    refine ebind_same fun y => ?_
    obtain ⟨l, g⟩ := y
    rcases l with _ | ⟨c0, _ | ⟨c2, _ | ⟨c3, l⟩⟩⟩
    · rfl
    · rfl
    · exact rounds_step g (rounds_blind es rs _ _)
    · rfl

/-! ## 4 The fold, the batching, the closing of a link, the frame's closing -/

/-- What the fold on the carried record returns, wiped. -/
def wipeRD {L : Type} (x : SingleRows × DState L) : SingleRows × DState L := (singleRowsWithZeroTarget x.1, wipeD x.2)

/-- What the fold returns, wiped. -/
def wipeRS (x : SingleRows × Statement) : SingleRows × Statement := (singleRowsWithZeroTarget x.1, wipeSt x.2)

/-- What the batching returns, wiped. -/
def wipeB (z : GroupRow × GroupLayout × Statement) : GroupRow × GroupLayout × Statement :=
  (wipeG z.1, z.2.1, wipeSt z.2.2)

/-- What the frame's closing returns, wiped. -/
def wipeFS (x : ReqFrame × Statement) : ReqFrame × Statement := (wipeFrame x.1, wipeSt x.2)

/-- **The fold on the carried record**, where the fresh mask came in an earlier message, at the wiped record and at
the record, and at two rows that differ in their targets alone: the same refusal, or values that are equal once
wiped. -/
theorem foldD_wiped {L : Type} (ft : Nat) (d : DState L) (F : FoldShape) {row row' : GroupRow}
    (h : wipeG row' = wipeG row) (fr : Nat) (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    (foldD ft (wipeD d) F row' (some fr) es rs).map wipeRD = (foldD ft d F row (some fr) es rs).map wipeRD := by
  have e1 : spendAsMaskL (wipeD d).st fr = spendAsMaskL d.st fr := spendAsMaskL_wipe d.st fr
  unfold VerifiableInference.Desc.First.Close.foldD
  cases es with
  | nil => cases rs <;> rfl
  | cons eE eR =>
    cases rs with
    | nil => rfl
    | cons rE rR =>
      dsimp only
      refine ebind_same fun _ => ?_
      refine ebind_same fun _ => ?_
      refine need_rel (foldShapeFits_wipe d.st F) ?_
      simp only [pure_bind]
      refine need_rel (foldMaskFits_wipe d.st F fr) ?_
      rw [e1, spendAsMaskP_wipe]
      refine ebind_same fun _ => ?_
      refine got_map wipeD fun d2 => ?_
      refine ebind_same fun y => ?_
      obtain ⟨l, eps⟩ := y
      rcases l with _ | ⟨sum, _ | ⟨s2, l⟩⟩
      · rfl
      · dsimp only
        refine need_rel (foldRowFits_rel d2.st F h) ?_
        refine ebind_rel (fun x : List E × E => x.1) (rounds_blind eR rR _ _) fun b b' hb => ?_
        obtain ⟨γ, c⟩ := b
        obtain ⟨γ', c'⟩ := b'
        have hγ : γ = γ' := hb
        subst hγ
        show (Except.ok (singleRowsWithZeroTarget (foldOutput (wipeSt d2.st) F row' fr eps γ c), wipeD (wipeD d2)) :
            Except String (SingleRows × DState L)) =
          Except.ok (singleRowsWithZeroTarget (foldOutput d2.st F row fr eps γ c'), wipeD d2)
        rw [foldOutput_rel d2.st F h fr eps γ c c', wipeD_idem]
      · rfl

/-- The fold at the wiped statement and at the statement, and at two rows that differ in their targets alone: the
same refusal, or values that are equal once wiped. -/
theorem fold_wiped (S : Statement) (F : FoldShape) {row row' : GroupRow} (h : wipeG row' = wipeG row) (mask : Nat)
    (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    (fold (wipeSt S) F row' mask es rs).map wipeRS = (fold S F row mask es rs).map wipeRS := by
  unfold VerifiableInference.Desc.First.Close.fold
  rw [emap_map, emap_map]
  exact emap_rel (wipeRD (L := Unit)) (foldD_wiped 0 (onSt S) F h mask es rs) fun b b' hb =>
    (congrArg (fun z : SingleRows × DState Unit => (z.1, z.2.st)) hb :)

/-- The fold at two statements that are equal once wiped, and at two rows that differ in their targets alone: the
same refusal, or values that are equal once wiped. -/
theorem fold_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) {row row' : GroupRow} (hr : wipeG row' = wipeG row)
    (F : FoldShape) (mask : Nat) (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    (fold S' F row' mask es rs).map wipeRS = (fold S F row mask es rs).map wipeRS := by
  rw [← fold_wiped S' F (rfl : wipeG row' = wipeG row') mask es rs, hS]
  exact fold_wiped S F hr mask es rs

/-- The batching at the wiped statement and at the statement: the same refusal, or values that are equal once wiped
(`bat_wipe`, Honest/K10/BatWipe.lean, with the same map on both sides). -/
theorem bat_alike (S : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) :
    (bat (wipeSt S) g e r).map wipeB = (bat S g e r).map wipeB := by
  have hb := bat_wipe S g e r
  cases h1 : bat S g e r with
  | error m =>
    cases h2 : bat (wipeSt S) g e r with
    | error m' =>
      rw [h1, h2] at hb
      have hm : m' = m := Except.error.inj hb
      subst hm
      rfl
    | ok y' =>
      rw [h1, h2] at hb
      cases hb
  | ok y =>
    cases h2 : bat (wipeSt S) g e r with
    | error m' =>
      rw [h1, h2] at hb
      cases hb
    | ok y' =>
      rw [h1, h2] at hb
      obtain ⟨row, L, S1⟩ := y
      obtain ⟨row', L', S1'⟩ := y'
      have e0 : (wipeG row', L', S1') = (wipeG row, L, wipeSt S1) := Except.ok.inj hb
      have e1 : wipeG row' = wipeG row := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.1) e0 :)
      have e2 : L' = L := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.2.1) e0 :)
      have e3 : S1' = wipeSt S1 := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.2.2) e0 :)
      show (Except.ok (wipeG row', L', wipeSt S1') : Except String (GroupRow × GroupLayout × Statement)) =
        Except.ok (wipeG row, L, wipeSt S1)
      rw [e1, e2, e3, wipeSt_idem]

/-- **The closing of a link** at the wiped statement and at the statement: the same refusal, or values that are
equal once wiped. -/
theorem closing_wiped (P : Plan) (S : Statement) (g : Nat) (mask : Option Nat) (rs : List Fmt.RoundView) :
    (closing P (wipeSt S) g mask rs).map wipeRS = (closing P S g mask rs).map wipeRS := by
  unfold VerifiableInference.Desc.First.Close.closing
  cases P.entries with
  | nil => cases rs <;> rfl
  | cons eB es =>
    cases rs with
    | nil => rfl
    | cons rB rs =>
      dsimp only
      refine ebind_same fun m => ?_
      refine ebind_rel wipeB (bat_alike S g eB rB) fun z z' hz => ?_
      obtain ⟨row', L', S1'⟩ := z
      obtain ⟨row, L, S1⟩ := z'
      have e1 : wipeG row' = wipeG row := (congrArg (fun t : GroupRow × GroupLayout × Statement => t.1) hz :)
      have e2 : L' = L := (congrArg (fun t : GroupRow × GroupLayout × Statement => t.2.1) hz :)
      have e3 : wipeSt S1' = wipeSt S1 := (congrArg (fun t : GroupRow × GroupLayout × Statement => t.2.2) hz :)
      subst e2
      dsimp only
      refine ebind_same fun _ => ?_
      exact fold_rel e3 e1 _ m es rs

/-- **The frame's closing of a link** at the wiped frame and statement and at the frame and statement: the same
refusal, or values that are equal once wiped. -/
theorem closeFrame_wiped (owed : Option Nat) (f : ReqFrame) (S : Statement) (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    (closeFrame owed (wipeFrame f) (wipeSt S) es rs).map wipeFS = (closeFrame owed f S es rs).map wipeFS := by
  unfold VerifiableInference.Desc.First.Close.closeFrame
  refine ebind_same fun _ => ?_
  refine ebind_same fun L => ?_
  refine ebind_same fun G => ?_
  refine ebind_same fun _ => ?_
  refine ebind_rel wipeRS (closing_wiped _ S f.group f.mask rs) fun b b' hb => ?_
  obtain ⟨r, T⟩ := b
  obtain ⟨r', T'⟩ := b'
  have e1 : singleRowsWithZeroTarget r = singleRowsWithZeroTarget r' := (congrArg (fun t : SingleRows × Statement => t.1) hb :)
  have e2 : wipeSt T = wipeSt T' := (congrArg (fun t : SingleRows × Statement => t.2) hb :)
  show (Except.ok (({ f with rows := singleRowsWithZeroTarget r, mask := none, link := f.link + 1, next := .first } : ReqFrame),
      wipeSt T) : Except String (ReqFrame × Statement)) =
    Except.ok ({ f with rows := singleRowsWithZeroTarget r', mask := none, link := f.link + 1, next := .first }, wipeSt T')
  rw [e1, e2]

/-! ## 5 K10's block at the first chain's state -/

/-- K10's part of the state, wiped. -/
def wipeRec (r : Rec) : Rec := { r with frame := wipeFrame r.frame, st := wipeSt r.st }

/-- K10's part of the wiped state is K10's part of the state, wiped. -/
theorem recOf_wipe (s : S) : recOf (wipeS s) = wipeRec (recOf s) := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Writing K10's part back and then wiping gives what writing the wiped part into the wiped state gives. -/
theorem putRec_wipe (s : S) (r : Rec) :
    wipeS (putRec s r) = putRec (wipeS s) (wipeRec r) := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The block's decision is one map over the frame's closing. -/
theorem closing_decide {Cl : Type} (P : Par) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.K9.closing (Cl := Cl) P).decide s rs gs =
      (closeFrame (recOf s).owed (recOf s).frame
        (recOf s).st (entries P) rs).map fun x =>
          putRec s ⟨none, x.1, x.2⟩ := by
  show ((closeFrame (recOf s).owed (recOf s).frame
      (recOf s).st (entries P) rs).map fun x => (⟨none, x.1, x.2⟩ : Rec)).map
        (putRec s) = _
  rw [emap_map]

/-- **K10's block decides at the wiped state as at the state**: the same refusal, or states that are equal once
wiped. It writes the frame's rows, whose target is the fold's last running claim, so the two states are equal
only once wiped. -/
theorem closing_wiped_at {Cl : Type} (P : Par) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    AlikeE wipeS ((VerifiableInference.Desc.K9.closing (Cl := Cl) P).decide (wipeS s) rs gs)
      ((VerifiableInference.Desc.K9.closing (Cl := Cl) P).decide s rs gs) := by
  refine AlikeE.of_eq ?_
  rw [closing_decide, closing_decide, emap_map, emap_map, recOf_wipe]
  refine emap_rel wipeFS (closeFrame_wiped (recOf s).owed (recOf s).frame
    (recOf s).st (entries P) rs) fun b b' hb => ?_
  have e1 : wipeFrame b.1 = wipeFrame b'.1 := (congrArg (fun t : ReqFrame × Statement => t.1) hb :)
  have e2 : wipeSt b.2 = wipeSt b'.2 := (congrArg (fun t : ReqFrame × Statement => t.2) hb :)
  show wipeS (putRec (wipeS s) ⟨none, b.1, b.2⟩) =
    wipeS (putRec s ⟨none, b'.1, b'.2⟩)
  rw [putRec_wipe, putRec_wipe, wipeS_idem]
  show putRec (wipeS s) ⟨none, wipeFrame b.1, wipeSt b.2⟩ =
    putRec (wipeS s) ⟨none, wipeFrame b'.1, wipeSt b'.2⟩
  rw [e1, e2]

/-- **K10's block**: at two states that are equal once wiped its decision refuses with the same word or returns
states that are equal once wiped; it has no run of claims and no run behind the batching. -/
theorem closing_whole2 {Cl : Type} (P : Par) : Whole2 wipeS (VerifiableInference.Desc.K9.closing (Cl := Cl) P) := by
  refine ⟨Decides2.of_wiped (fun _ _ _ _ => rfl) (closing_wiped_at P), ?_, ?_⟩
  · intro c hc
    have h0 : (VerifiableInference.Desc.K9.closing (Cl := Cl) P).claims = [] := rfl
    rw [h0] at hc
    cases hc
  · intro c hc
    have h0 : (VerifiableInference.Desc.K9.closing (Cl := Cl) P).after = [] := rfl
    rw [h0] at hc
    cases hc

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ebind_rel
#print axioms ProofFile.Honest.K10.emap_rel
#print axioms ProofFile.Honest.K10.all_same
#print axioms ProofFile.Honest.K10.any_same
#print axioms ProofFile.Honest.K10.foldShapeFits_wipe
#print axioms ProofFile.Honest.K10.foldMaskFits_wipe
#print axioms ProofFile.Honest.K10.foldRowFits_rel
#print axioms ProofFile.Honest.K10.foldOutput_rel
#print axioms ProofFile.Honest.K10.rounds_step
#print axioms ProofFile.Honest.K10.rounds_blind
#print axioms ProofFile.Honest.K10.wipeRD
#print axioms ProofFile.Honest.K10.wipeRS
#print axioms ProofFile.Honest.K10.wipeB
#print axioms ProofFile.Honest.K10.wipeFS
#print axioms ProofFile.Honest.K10.foldD_wiped
#print axioms ProofFile.Honest.K10.fold_wiped
#print axioms ProofFile.Honest.K10.fold_rel
#print axioms ProofFile.Honest.K10.bat_alike
#print axioms ProofFile.Honest.K10.closing_wiped
#print axioms ProofFile.Honest.K10.closeFrame_wiped
#print axioms ProofFile.Honest.K10.wipeRec
#print axioms ProofFile.Honest.K10.recOf_wipe
#print axioms ProofFile.Honest.K10.putRec_wipe
#print axioms ProofFile.Honest.K10.closing_decide
#print axioms ProofFile.Honest.K10.closing_wiped_at
#print axioms ProofFile.Honest.K10.closing_whole2
