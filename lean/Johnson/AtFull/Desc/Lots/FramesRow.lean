-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/FramesRow.lean: TOWARDS AN EXAMPLE OF THE HEAD BY LEAN's KERNEL:
THE ROW OF ONE LOT OF THE PROOF FILE's DESCRIPTION: THE LINKS' FRAMES (ProofFile.framesLot,
Johnson/Desc/ProofFile/Lots/PureLots.lean): its blocks' skeletons (ProofFile.Sk.Skel,
Johnson/Desc/ProofFile/Law/Skel/Skel.lean: a block less its functions) ARE THE WRITTEN ONES, UNDER
SIX HYPOTHESES BY FIELD ON WHAT THE LOT READS OF THE PUBLIC PART Z. No scope, no opening, no pin is
spent. THE MAP. The lot's blocks are, for each row f of the frames' maker framesOf
(Johnson/Top/H0/Walk/FrameLot.lean), three blocks without a round: «link l: lay | opened | clear» at
the pieces 0 | 1 | f.last; the second bears f.plan as its test on the plan. The ground G is not
read. So the skeletons hang on (f.link, f.plan, f.last) alone. WHERE THE MAKER REFUSES THE LOT GIVES
ONE BLOCK THAT REFUSES AT RUN TIME AND WHOSE TEST ON THE PLAN ACCEPTS: so «the lot returns» says
nothing: what is shown is that the maker returns.
  tri · skel3 · skel_opened · retype_quiet · retype_quiet0 · skel_frame  a frame's three skeletons
  lot_skel (T1)     the lot's skeletons, where the maker returns. General
  viewL · sameB     THE VIEW, BY FIELD: of a link's built structure: kind · fv · g (not at the
                    head's link); at a layers' link: it bears the whole list Tp.nt of its plan's
                    entry (one member for each array) and that entry's fork's sizes
  flagV · plainV · triAt · triV  the maker's text, on the view, with its own words of refusal
                    mapM_map_eq · view_at · plain_at · flag_at · pub_Tp · pub_Fp
  tri_of_view (T2)  the maker, read down to the triples, IS its text on the view: an equation, the
                    refusals among it. General
  viewW · plainW · triW · framesRowsW  the written values: 25 links; 75 rows
  tri_written (T3)  at the written view every link has its frame and every test on the plan accepts:
                    by decide +kernel
  tri_kind_turned   · tri_same_turned · tri_short · tri_shortG · tri_plain_turned · tri_p4_turned
                    six negatives, by the kernel: each of the six hypotheses, turned, gives another
                    answer
  cols              · rows_in_cut (T4) · rows_in_cut_turned A CONTROL AGAINST THE WRITTEN CUT
                    (cutFirstFull, Johnson/Desc/Ok/PlanWritten/CutLit.lean): the 50 rows at a link's
                    first and last piece are, but for the name and in order, its rows «link l: laid»
                    and «link l: cleared»; with the head's end at piece 13 they are not
  plain_written (T7)  a control against the written shape: its first 24 links have no plain scalar
                    triAt_take · mapM_congr_mem
  frames_row (T5)   THE ROW: the maker returns, and ((framesLot Z).blocks G).map skel = framesRowsW
                    framesLotW · frames_lotSk (T6) · frames_steady the same in lotSk's form; the lot
                    is steady
  hypsB · frames_lotSk_of_B  the six hypotheses as one test with code; the row from its accept
THE NAMES. The rows bear the lot's blocks' own names («link l: lay» …), as lotSk reads them; the
written cut's rows bear the seat's («link l: laid» …): T4 compares the other columns.
MORE THAN IS SPENT. At an attention link no test on the plan reads g: it enters through «the
attention's plan number g is there» alone: viewW's g there could be any number below 12.
LIMITS. THE SIX HYPOTHESES ARE PAID NOWHERE HERE; that any public files meet them is not shown by
Lean. viewW follows the pattern of the library's own test of the links' lister at two groups
(OnBytes/Model/TestStagesLinks.lean) and two texts of the full size's kinds. At VerifierAndGoals.storedPublicFiles's
public part (synthetic weights) Lean's evaluator has once said true of all six together (hypsB):
evidence, no proof; the file that asked it is not in this library. T4 IS NO INDEPENDENT WITNESS: the
written cut was printed off the description that this lot helps to make: it shows that the two
written tables agree, no more; and it does not reach the 25 rows «opened». The full size alone.
Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20.Row
open OnBytes OnBytes.Model
open ProofFile (Pub Ground Lot framesLot frameBlocks)
open ProofFile.Sk (Skel skel skel_quiet skel_retype)
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (planFlag planPlain planLay planAtt planLayZero sizes)
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame frameAt zeroAt headFrame pubOf)

/-- What a frame's three blocks' skeletons hang on. -/
def tri (f : LinkFrame) : ℕ × Bool × ℕ := (f.link, f.plan, f.last)

/-- The three skeletons of a link's frame. -/
def skel3 (t : ℕ × Bool × ℕ) : List Skel :=
  [Skel.quiet s!"link {t.1}: lay" 1 (some t.1) 0,
   { Skel.quiet s!"link {t.1}: opened" 1 (some t.1) 1 with planOk := t.2.1 },
   Skel.quiet s!"link {t.1}: clear" 1 (some t.1) t.2.2]

theorem skel_opened (n : String) (l p : ℕ) (plan : Bool) (g : S → Except String S) :
    skel ({ roundlessBlock n 1 (some l) p g with planOk := plan } : Block S Unit) =
      { Skel.quiet n 1 (some l) p with planOk := plan } := by
  simp [skel, roundlessBlock, Skel.quiet, ProofFile.Sk.toldFrom]

theorem retype_quiet (n : String) (l p : ℕ) (plan : Bool) :
    ({ Skel.quiet n 1 (some l) p with planOk := plan } : Skel).retype =
      { Skel.quiet n 1 (some l) p with planOk := plan } := by
  simp [Skel.retype, Skel.quiet]

theorem retype_quiet0 (n : String) (l p : ℕ) :
    (Skel.quiet n 1 (some l) p).retype = Skel.quiet n 1 (some l) p := by
  simp [Skel.retype, Skel.quiet]

theorem skel_frame (f : LinkFrame) :
    ((frameBlocks f.link f.plan f.lay f.opened f.clear 1 f.last).map fun b =>
      skel (b.retype : Block S ProofFile.Cl)) = skel3 (tri f) := by
  unfold frameBlocks skel3 tri
  simp only [List.map_cons, List.map_nil, skel_retype, skel_quiet, skel_opened, retype_quiet,
    retype_quiet0]

/-- **T1. The lot's skeletons, where the frames' maker returns.** -/
theorem lot_skel {Z : Pub} {fs : List LinkFrame}
    (h : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (G : Ground) :
    ((framesLot Z).blocks G).map skel = (fs.map tri).flatMap skel3 := by
  show ((ProofFile.asCl (fun _ => P1L20.blocksOf Z) G ++ []).map skel) = _
  unfold ProofFile.asCl P1L20.blocksOf
  rw [h, List.append_nil, List.map_map, List.map_flatMap, List.flatMap_map]
  exact List.flatMap_congr fun f _ => skel_frame f

/-! ## The view, by field -/

/-- What the frames' maker's tests on the plan read of a link's built structure, but for the two
comparisons with the plan's entry (sameB). The group's number is not read at the head's link. -/
def viewL (X : Stages.LinkH) : ℕ × Bool × ℕ := (X.kind, X.fv, if X.kind == 2 then 0 else X.g)

/-- At a layers' link (kind 0): the built structure bears the whole list Tp.nt of its plan's entry
(one member for each array) and its planned fork's sizes. TRUE AT EVERY OTHER LINK, and where there
is no such entry: the maker makes the comparison in its two layers' arms alone. -/
def sameB (built : Array Stages.LinkH) (W : Verify.Public) (l : ℕ) : Bool :=
  match built[l]? with
  | none => true
  | some X =>
    if X.kind == 0 then
      match W.G[X.g]? with
      | none => true
      | some hp => X.Tp.nt == hp.Tp.nt && sizes X.Fp == sizes hp.Fp
    else true

def flagV (v : ℕ × Bool × ℕ) (kind : ℕ) : Bool := v.1 == kind && v.2.1 == (kind != 1)

def plainV (plain : List ℕ) (v : ℕ × Bool × ℕ) (l : ℕ) : Bool :=
  plain[l]? == some (if v.1 == 2 then 1 else 0)

/-- **The frames' maker's text, on the view**: at link l: its number, its test on the plan, the
piece of its end. -/
def triAt (Ls : List (ℕ × Bool × ℕ)) (nG nA : ℕ) (p4 : Bool) (plain : List ℕ) (same : ℕ → Bool)
    (l : ℕ) : Except String (ℕ × Bool × ℕ) :=
  if ((Ls[l]?).map fun v => v.1 == 2).getD false then
    match Ls[l]? with
    | none => .error s!"no plan: link {l}'s letters are not there"
    | some v => .ok (l, flagV v 2, 15)
  else if l == 0 then
    match Ls[0]? with
    | none => .error "no plan: link 0's letters are not there"
    | some v =>
      if v.1 != 0 || !decide (v.2.2 < nG) then .error "no plan: link 0's letters are not there"
      else .ok (0, plainV plain v 0 && 0 == (if p4 then 2 * v.2.2 else v.2.2) && same 0 &&
        flagV v 0, 13)
  else
    match Ls[l]? with
    | none => .error s!"no plan: link {l}'s letters are not there"
    | some v =>
      if v.1 == 1 then
        if v.2.2 < nA then .ok (l, l != 0 && plainV plain v l && flagV v 1, 13)
        else .error s!"no plan: link {l}'s letters are not there"
      else if v.1 == 0 then
        if v.2.2 < nG then
          .ok (l, l != 0 && plainV plain v l && l == (if p4 then 2 * v.2.2 else v.2.2) && same l &&
            flagV v 0, 13)
        else .error s!"no plan: link {l}'s letters are not there"
      else .error s!"no plan: link {l}'s letters are not there"

def triV (Ls : List (ℕ × Bool × ℕ)) (nG nA : ℕ) (p4 : Bool) (plain : List ℕ) (same : ℕ → Bool) :
    Except String (List (ℕ × Bool × ℕ)) :=
  (List.range Ls.length).mapM (triAt Ls nG nA p4 plain same)

theorem mapM_map_eq {α β γ : Type} {f : α → Except String β} {g : α → Except String γ}
    {h : β → γ} (H : ∀ a, (f a).map h = g a) :
    ∀ l : List α, (l.mapM f).map (List.map h) = l.mapM g
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, ← H a, ← mapM_map_eq H l]
    cases f a with
    | error e => rfl
    | ok b =>
      cases l.mapM f with
      | error e => rfl
      | ok bs => rfl

theorem view_at (built : Array Stages.LinkH) (l : ℕ) :
    (built.toList.map viewL)[l]? = (built[l]?).map viewL := by
  rw [List.getElem?_map, Array.getElem?_toList]

theorem plain_at (shape : Params.ReqShape) (X : Stages.LinkH) (l : ℕ) :
    planPlain shape (pubOf X) l = plainV (shape.link.map (·.plain)) (viewL X) l := by
  unfold planPlain plainV
  rw [List.getElem?_map]
  rfl

theorem flag_at (X : Stages.LinkH) (kind : ℕ) : planFlag (pubOf X) kind = flagV (viewL X) kind :=
  rfl

theorem pub_Tp (X : Stages.LinkH) : (pubOf X).Tp = X.Tp := rfl

theorem pub_Fp (X : Stages.LinkH) : (pubOf X).Fp = X.Fp := rfl

/-- **T2. The frames' maker, read down to the triples, is its text on the view.** General. -/
theorem tri_of_view (built : Array Stages.LinkH) (first : Params.First) (W : Verify.Public) :
    (framesOf built first W).map (List.map tri) =
      triV (built.toList.map viewL) W.G.size W.A.size W.layers.y.h.p4
        (first.shape.link.map (·.plain)) (sameB built W) := by
  unfold framesOf triV
  rw [List.length_map, Array.length_toList]
  refine mapM_map_eq (fun l => ?_) _
  unfold triAt
  rw [view_at, view_at]
  cases hX : built[l]? with
  | none =>
    by_cases h0 : l = 0
    · subst h0
      simp [hX, zeroAt, Except.map]
    · simp [hX, h0, frameAt, Except.map]
  | some X =>
    by_cases h2 : X.kind = 2
    · simp [h2, viewL, flagV, Except.map, tri, headFrame, planFlag, pubOf]
    · have hv : viewL X = (X.kind, X.fv, X.g) := by simp [viewL, h2]
      by_cases h0 : l = 0
      · subst h0
        by_cases hk : X.kind = 0
        · cases hG : W.G[X.g]? with
          | none =>
            have hlt : ¬ X.g < W.G.size := by
              intro h
              rw [Array.getElem?_eq_getElem h] at hG
              cases hG
            simp [hX, hv, hk, hlt, zeroAt, Except.map]
          | some hp =>
            have hlt : X.g < W.G.size := by
              by_contra h
              rw [Array.getElem?_eq_none (by omega)] at hG
              cases hG
            simp [hX, hv, hk, hlt, zeroAt, Except.map, tri, planLayZero, plain_at, flag_at,
              sameB, pub_Tp, pub_Fp, Bool.and_assoc]
        · simp [hX, h2, hv, hk, zeroAt, Except.map]
      · by_cases h1 : X.kind = 1
        · cases hA : W.A[X.g]? with
          | none =>
            have hlt : ¬ X.g < W.A.size := by
              intro h
              rw [Array.getElem?_eq_getElem h] at hA
              cases hA
            simp [hX, hv, h0, h1, hlt, frameAt, Except.map]
          | some p =>
            have hlt : X.g < W.A.size := by
              by_contra h
              rw [Array.getElem?_eq_none (by omega)] at hA
              cases hA
            simp [hX, hv, h0, h1, hlt, frameAt, Except.map, tri, planAtt, plain_at,
              flag_at, Bool.and_assoc]
        · by_cases hk : X.kind = 0
          · cases hG : W.G[X.g]? with
            | none =>
              have hlt : ¬ X.g < W.G.size := by
                intro h
                rw [Array.getElem?_eq_getElem h] at hG
                cases hG
              simp [hX, hv, h0, hk, hlt, frameAt, Except.map]
            | some hp =>
              have hlt : X.g < W.G.size := by
                by_contra h
                rw [Array.getElem?_eq_none (by omega)] at hG
                cases hG
              simp [hX, hv, h0, hk, hlt, frameAt, Except.map, tri, planLay, plain_at,
                flag_at, sameB, pub_Tp, pub_Fp, Bool.and_assoc]
          · simp [hX, h2, hv, h0, h1, hk, frameAt, Except.map]

/-! ## The written values, and the closed facts -/

/-- The 25 links' views at the full size: twelve times a layers' and an attention link of one group,
then the head's. -/
def viewW : List (ℕ × Bool × ℕ) :=
  (List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)]

/-- No plain scalar at the 24 links in front of the head's. (The head's frame asks nothing of
it.) -/
def plainW : List ℕ := List.replicate 24 0

def triW : List (ℕ × Bool × ℕ) := (List.range 25).map fun l => (l, true, if l == 24 then 15 else 13)

/-- **The frames' lot's written skeletons**: 75 rows. -/
def framesRowsW : List Skel := triW.flatMap skel3

/-- **T3. At the written view every link has its frame, and every test on the plan accepts.** -/
theorem tri_written : triV viewW 12 12 true plainW (fun _ => true) = .ok triW := by decide +kernel

/-- Negative: an attention link's kind turned to the head's: another row. -/
theorem tri_kind_turned :
    (triV (viewW.set 1 (2, false, 0)) 12 12 true plainW (fun _ => true) == .ok triW) = false := by
  decide +kernel

/-- Negative: one comparison with the plan's entry fails: a test on the plan rejects. -/
theorem tri_same_turned :
    (triV viewW 12 12 true plainW (fun l => l != 4) == .ok triW) = false := by decide +kernel

/-- Negative: eleven attention plans: the maker refuses. -/
theorem tri_short : (triV viewW 12 11 true plainW (fun _ => true)).toOption = none := by
  decide +kernel

/-- Negative: eleven layers' plans: the maker refuses. -/
theorem tri_shortG : (triV viewW 11 12 true plainW (fun _ => true)).toOption = none := by
  decide +kernel

/-- Negative: a plain scalar at link 7. -/
theorem tri_plain_turned :
    (triV viewW 12 12 true (plainW.set 7 1) (fun _ => true) == .ok triW) = false := by
  decide +kernel

/-- Negative: attention links do not stand between the layers'. -/
theorem tri_p4_turned :
    (triV viewW 12 12 false plainW (fun _ => true) == .ok triW) = false := by decide +kernel

/-- A row of the written cut, of a skeleton: its columns but the name; of the told rounds their
number (it is 0 at every row here). -/
def cols (k : Skel) : VerifiableInference.Desc.Place × ℕ × ℕ × ℕ × List (ℕ × ℕ) :=
  (k.place, k.nRounds, k.nOracles, k.told.length, k.before)

set_option maxRecDepth 1000000 in
/-- **T4. A control against the written cut**: the 50 written rows at a link's first and last
piece are, but for the name and in order, the written cut's rows «link l: laid» and «link l:
cleared». (The 25 rows «opened» are joined behind the block at piece 1 by the seat: they have no
row of their own there.) -/
theorem rows_in_cut :
    (((framesRowsW.filter fun k => k.place.piece != 1).map cols) ==
      ((VerifiableInference.PlanWritten.cutFirstFull.filter fun r =>
        r.1.endsWith ": laid" || r.1.endsWith ": cleared").map fun r =>
          (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1.length, r.2.2.2.2.2))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative for T4: with the head's end at piece 13 the rows are not the written cut's. -/
theorem rows_in_cut_turned :
    ((((((List.range 25).map fun l => (l, true, 13)).flatMap skel3).filter fun k =>
        k.place.piece != 1).map cols) ==
      ((VerifiableInference.PlanWritten.cutFirstFull.filter fun r =>
        r.1.endsWith ": laid" || r.1.endsWith ": cleared").map fun r =>
          (r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1.length, r.2.2.2.2.2))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **T7. A control against the written shape**: its first 24 links have no plain scalar. -/
theorem plain_written :
    (VerifiableInference.PlanWritten.proofSizedFull.request.link.map (·.plain)).take 24 =
      plainW := by decide +kernel

/-! ## The row -/

/-- plainV reads the first 24 entries alone, at a link in front of the head's. -/
theorem triAt_take (Ls : List (ℕ × Bool × ℕ)) (nG nA : ℕ) (p4 : Bool) (plain : List ℕ)
    (same same' : ℕ → Bool) (hs : ∀ l < 25, same l = same' l) (l : ℕ) (hl : l < 25)
    (h24 : (Ls[24]?).map (fun v => v.1 == 2) = some true) :
    triAt Ls nG nA p4 plain same l = triAt Ls nG nA p4 (plain.take 24) same' l := by
  by_cases e : l = 24
  · subst e
    unfold triAt
    rw [h24]
    rfl
  · have hp : ∀ v, plainV plain v l = plainV (plain.take 24) v l := by
      intro v
      unfold plainV
      rw [List.getElem?_take_of_lt (by omega)]
    have hp0 : ∀ v, plainV plain v 0 = plainV (plain.take 24) v 0 := by
      intro v
      unfold plainV
      rw [List.getElem?_take_of_lt (by omega)]
    unfold triAt
    simp only [hp, hp0, hs l hl, hs 0 (by omega)]

theorem mapM_congr_mem {α β : Type} {f g : α → Except String β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_congr_mem l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **T5. THE FRAMES' LOT's ROW, UNDER SIX HYPOTHESES BY FIELD**: the frames' maker returns, and the
lot's blocks' skeletons are the written ones. The ground G is not read. -/
theorem frames_row {Z : Pub} (hL : Z.p.built.links.toList.map viewL = viewW)
    (hG : Z.p.X.G.size = 12) (hA : Z.p.X.A.size = 12) (h4 : Z.p.X.layers.y.h.p4 = true)
    (hP : (Z.first.shape.link.map (·.plain)).take 24 = plainW)
    (hS : ∀ l < 25, sameB Z.p.built.links Z.p.X l = true) (G : Ground) :
    (∃ fs, framesOf Z.p.built.links Z.first Z.p.X = .ok fs) ∧
      ((framesLot Z).blocks G).map skel = framesRowsW := by
  have h := tri_of_view Z.p.built.links Z.first Z.p.X
  rw [hL, hG, hA, h4] at h
  have e : triV viewW 12 12 true (Z.first.shape.link.map (·.plain))
      (sameB Z.p.built.links Z.p.X) = .ok triW := by
    rw [← tri_written, ← hP]
    unfold triV
    refine mapM_congr_mem _ fun l hl => ?_
    have hl' : l < 25 := by
      have := List.mem_range.1 hl
      simpa [viewW] using this
    exact triAt_take viewW 12 12 true _ _ _ hS l hl' (by decide)
  rw [e] at h
  cases hf : framesOf Z.p.built.links Z.first Z.p.X with
  | error x =>
    rw [hf] at h
    cases h
  | ok fs =>
    rw [hf] at h
    have ht : fs.map tri = triW := Except.ok.inj h
    refine ⟨⟨fs, rfl⟩, ?_⟩
    rw [lot_skel hf G, ht]
    rfl

/-- The frames' lot's written skeleton, in lotSk's form. -/
def framesLotW : ProofFile.Sk.LotSk :=
  { name := "the links' frames", letters := false, still := [], blocks := framesRowsW
    batch := fun _ => none, each := fun _ => false, tests := fun _ => false }

/-- **T6. The same in lotSk's form.** -/
theorem frames_lotSk {Z : Pub} (hL : Z.p.built.links.toList.map viewL = viewW)
    (hG : Z.p.X.G.size = 12) (hA : Z.p.X.A.size = 12) (h4 : Z.p.X.layers.y.h.p4 = true)
    (hP : (Z.first.shape.link.map (·.plain)).take 24 = plainW)
    (hS : ∀ l < 25, sameB Z.p.built.links Z.p.X l = true) (G : Ground) :
    ProofFile.Sk.lotSk G (framesLot Z) = framesLotW := by
  unfold ProofFile.Sk.lotSk framesLotW
  rw [(frames_row hL hG hA h4 hP hS G).2]
  rfl

/-- The lot supplies no batching: so it is steady. -/
theorem frames_steady (Z : Pub) (G : Ground) : ProofFile.Sk.Steady G (framesLot Z) :=
  ProofFile.Sk.steady_none G _ fun _ => rfl

/-- **The six hypotheses, as one test with code**, for an evaluation at given public files. -/
def hypsB (Z : Pub) : Bool :=
  decide (Z.p.built.links.toList.map viewL = viewW) && Z.p.X.G.size == 12 && Z.p.X.A.size == 12 &&
    Z.p.X.layers.y.h.p4 && decide ((Z.first.shape.link.map (·.plain)).take 24 = plainW) &&
    (List.range 25).all fun l => sameB Z.p.built.links Z.p.X l

/-- The row from the test's accept. -/
theorem frames_lotSk_of_B {Z : Pub} (h : hypsB Z = true) (G : Ground) :
    ProofFile.Sk.lotSk G (framesLot Z) = framesLotW := by
  unfold hypsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hL, hG⟩, hA⟩, h4⟩, hP⟩, hS⟩ := h
  exact frames_lotSk hL hG hA h4 hP hS G

end P1L20.Row

#print axioms P1L20.Row.frames_lotSk_of_B

#print axioms P1L20.Row.mapM_congr_mem
#print axioms P1L20.Row.frames_row
#print axioms P1L20.Row.frames_lotSk
#print axioms P1L20.Row.frames_steady

#print axioms P1L20.Row.rows_in_cut_turned
#print axioms P1L20.Row.plain_written
#print axioms P1L20.Row.triAt_take

#print axioms P1L20.Row.tri_written
#print axioms P1L20.Row.tri_kind_turned
#print axioms P1L20.Row.tri_same_turned
#print axioms P1L20.Row.tri_short
#print axioms P1L20.Row.tri_shortG
#print axioms P1L20.Row.tri_plain_turned
#print axioms P1L20.Row.tri_p4_turned
#print axioms P1L20.Row.rows_in_cut

#print axioms P1L20.Row.view_at
#print axioms P1L20.Row.plain_at
#print axioms P1L20.Row.flag_at
#print axioms P1L20.Row.pub_Tp
#print axioms P1L20.Row.pub_Fp
#print axioms P1L20.Row.tri_of_view

#print axioms P1L20.Row.mapM_map_eq

#print axioms P1L20.Row.skel_opened
#print axioms P1L20.Row.retype_quiet
#print axioms P1L20.Row.retype_quiet0
#print axioms P1L20.Row.skel_frame
#print axioms P1L20.Row.lot_skel
