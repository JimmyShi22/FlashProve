-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarHeavy.lean: **THE FIELD hCar OF THE CLOSING's FILES'
  STRUCTURE `K10Heavy` (Johnson/Desc/First/Close/Law/K10Heavy.lean: what K10's assembled law asks at
  a link), IN ITS OWN TEXT, AS A THEOREM's END**, at the names Nm := namesOf cs lo (stageOf gs 219)
  radFull kb hM hZ no and the fresh mask's word mW b := mWRaw … (strsOf F b.2) tree skip aF. By one
  call of `hCar_end` (HCarEnd.lean), with `behind_of_close` (BehindOfClose.lean), `layout_behind`
  and `closeFrame_reads` (CloseReads.lean) and `hSh_of_cf` (ShownOfCf.lean). The
  letters are K10Heavy's own, in their order, but Nm and mW; the end's text is cut out of
  K10Heavy.lean by program, with the two terms laid in. A theorem.

  `hCar_heavy`: from:
    hTie: the table's relation at the items that go out behind K10's place gives the item «carry» as
      the closed constant has it (carryAtZ);
    CLOSED, ON THE PLAN AND THE WRITTEN LISTS: hW · hr · hgood · hLA · hle · hord · hS · hPl · hsB ·
      hbD · hpos · hPC · hfs · hfa · hfskip;
    hShp, UNDER X: ShapesAre at whatever group the statement has at the frame's group: the clause
      «shapes» of K10Heavy's own field hX;
    hCfX: K10Heavy's own field of that name;
    hFront, UNDER X, AT THE STATE IN FRONT: statement and book are in step · the three tests on the
      book · the plan's list has (tree, tnF) at the frame's mask · the first places of the plan's
      list, as many as the book has, name trees below the base · the frame's group of the link has
      gs's two numbers;
    hDoor, UNDER X, THE CLOSING's OWN YES AND ITS WRITING: hH under «the way in answers» · «the book
      behind the
      switch's sending is there»;
    h2, UNDER X: the second half of CarriedAt.
  K10's law's condition in front (K10OnS) is not spent.
WHAT IS NO PREMISE:
  «the statement has a group there», the four sizes, and three of the four facts on the front are no
  premises (off the closing's own yes); ShownAt comes from hCfX.
  planClosedB (hPC: no state) is the closed part of planPubB, and «the frame's
  mask is below the book's places» is no premise: both bounds come from «statement and book
  are in step», ShapesAre and the closing's own yes.
  «the fresh mask's tree is below the base» and the two bounds by the first chain's
  number of trees are no premises: the first comes, under X, from «the first places of the
  plan's list name trees below the base» (a clause of hFront: below_at ends
  in it); the two from hbD: the base is at most the first chain's number of trees.
hDoor HAS THE CLOSING's OWN YES AMONG ITS HYPOTHESES (K10's end has it in hand). Without it
  hDoor would be asked at every state behind that is «the state in front
  but for the frame and the statement»: that holds at EVERY frame and statement, also at a statement
  with one message more, which is out of step with the book: there the book behind the sending is
  not there: hDoor could be met only where X has no member, and the theorem would be idle.

Limits. EVERY PREMISE NAMED ABOVE STANDS; NONE IS SHOWN HERE. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.K10Heavy
import Johnson.Desc.First.Link.Law.HCarEnd
import Johnson.Desc.First.Link.Law.BehindOfClose
import Johnson.Desc.First.Link.Law.ShownOfCf
import Johnson.Desc.First.Link.Law.PlanClosedB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowSays wordsAtFirst laysSeats)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First.K2Caller (SeatFitAt doorZ carryAtZ)
open _root_.Tw.K2 (switchNotices)

local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

/-- **THE FIELD hCar, IN ITS OWN TEXT.** -/
theorem hCar_heavy
    (cs : OnBytes.Codes)
    (lo : List (OracleShape × ℕ))
    (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = (stageOf gs
      219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = (stageOf gs
      219).Z)
    (keep : (sigOf cs lo).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf cs lo).Wit × Wp)
    (w₁ : LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
      (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp
      Wp)
    {Xi : Type}
    (Gd : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ)
    (L : List (BatFoldCaller GE))
    {Pz : Type}
    (smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) → Option
      ((sigOf cs s.l).om i).Smp)
    (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
    (σ₀ : (sigOf cs lo).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    {F : Frame}
    {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells)
    (c₀ : Cells)
    (tokOf : Pz × S1 → Tok)
    (pS : ∀ as : (Σ a : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.A, ((sigOf cs lo).om
      a.1).Z.S), ((sigOf cs lo).om as.1.1).Z.D →
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block S1 Cl)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → Wit Cells
      Tok MsgT → Wit Cells Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM
    hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf
    gs 219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
    gs.k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo))
    (Nu : Numbers)
    (Mg : Meaning Pz (Wit Cells Tok MsgT))
    (links : List ModelPart)
    (ps : List Place)
    (k : ℕ)
    (p : Place)
    (X : (Pz × S1) × F.E.Str → Prop)
    (O : List Item)
    (no : Fin lo.length → ℕ)
    (row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT)))
    (k' : ℕ)
    (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (D : WholeD) (hW : ProofFile.wholeAt Z = some D)
    (tree tnF skip aF : ℕ) (Lp : VerifiableInference.Desc.K12.Door.Laid) (shF0 : TreeShape)
    (hTie : ∀ (s : (Pz × S1) × F.E.Str) w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps
      k) s w → carryAtZ Z lay m s.1 (strsOf F s.2) w)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → (∃ t₀, stageOf gs 219 = stageOf r.g t₀) ∧ (∀
            n, keptRowsAt r.lo r.mem r.kp n = keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) ∧
      r.rad ≤ radFull)
    (hgood : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Good) (hLA : LayoutAgrees lo kb)
      (hle : gs.h ≤ gs.k)
    (hord : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → ∀ i : Fin lo.length, memMain lo i → kb i =
      true → (keptNosOf lo kb)[r.kept.idxOf i.val]? = some (posOf lo i))
    (hS : ∀ b : {i // memMain lo i}, SeatFitAt Gd cs lo seat b.1)
    (hPl : ∀ b : {i // memMain lo i}, Lp.places[no b.1]? = some (seat b.1))
    (hsB : ∀ i, (seat i).1 < base) (hbD : base ≤ D.t₁)
    (hpos : 2 ^ (stageOf gs 219).C.a ≤ 2 ^ (ProofFile.pAtK2 Z m).logN)
    (hfs : Lp.shapes[tree]? = some shF0) (hfa : shF0.logN = aF)
    (hfskip : shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip)
    (hShp : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → ∀ Gr, (rdK a.1).2.2.groups[(rdK
      a.1).2.1.group]? = some Gr → ShapesAre (rdK a.1).2.2 Gr lo kb no)
    (hCfX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → ∀ i, CfAt Gd cs lo seat (fun q => smpS q
      ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hPC : ∀ b : {i // memMain lo i}, planClosedB Gd Lp (no b.1) (seat b.1) (aOf cs (lo.get b.1).1)
      = true)
    (hFront : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → a.1.book.place.size = a.1.st.oracles.size
      ∧ VerifiableInference.Desc.K12.Door.atFirstBook (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree a.1
      = true ∧ VerifiableInference.Desc.K12.Door.atFirstSeats Lp a.1 = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits a.1 = true ∧ (∀ mk, (rdK a.1).2.1.mask = some mk
      → Lp.places[mk]? = some (tree, tnF)) ∧
      VerifiableInference.Desc.K12.Door.placesBelowB Lp a.1.book.place.size base = true ∧
      ∀ Gf, (rdK a.1).2.1.groups[(rdK a.1).2.1.link]? = some Gf → Gf.k = gs.k ∧ Gf.h = gs.h)
    (hDoor : ∀ z (a a' : S1 × F.E.Str) es rs, X ((z, a.1), a.2) →
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 es rs = .ok (rdBK a'.1) →
      a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 →
      (∀ t, doorZ Z m a'.1 = some t → (ProofFile.pAtK2 Z m).stands = .head → ∀ b, a'.1.here ≠
      .head b) ∧ ∀ t fx', doorZ Z m a'.1 = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      ∃ Bk, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
      (switchNotices fx'.T fx'.others) = some Bk)
    (h2 : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → ∃ (zz : (ZV (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) n num).D) (v : ((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull
      kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Wit ×
      Wp), (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK
      cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).over A₀).relR ((batX ((groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (faK10 Gd cs lo
      seat (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (namesOf cs lo (stageOf gs 219)
      radFull kb hM hZ no) keep (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)) n num
      fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ (fun b : S1 × F.E.Str =>
      mWRaw cs lo (memMain lo) (stageOf gs 219) radFull (fun i => layAt (sizesM lo kb) i.val) (fun i
      => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) (strsOf F b.2) tree skip aF) z a).1
      zz).2, ((ldBrG (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull
      kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n
      num)).kp E₀).map (e₀, wordsOf Gd cs lo seat (strsOf F a.2))).2) v) :
    ∀ z a a', X ((z, a.1), a.2) → K10OnS (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)
      (namesOf cs lo (stageOf gs 219) radFull kb hM hZ no)
    keep (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)) n num fx1 A₀ (placeFull
    gs.k).bC (placeFull gs.k).bZ w₀ w₁ L pS Pr (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat
    (namesOf cs lo (stageOf gs 219) radFull kb hM hZ no) L smpD σ₀ st₀ e₀ (fun b : S1 × F.E.Str =>
      mWRaw cs lo (memMain lo) (stageOf gs 219) radFull (fun i => layAt (sizesM lo kb) i.val) (fun i
      => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true) (strsOf F b.2) tree skip aF) z) a →
      K10EndS (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (namesOf cs lo (stageOf gs 219)
      radFull kb hM hZ no)
      keep (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)) n num fx1 A₀ (placeFull
    gs.k).bC
    (placeFull gs.k).bZ w₀ w₁ L (dBat n) dEps dTwo Pr b base (fun a τ w => ((pieceOf (held b) base
    ((dBat n) :: dEps :: List.replicate (Yc ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).foldCaller keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219)
    radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num) ((1 : Fin 3),
    (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dTwo) [] (restCap ex ix
    _)).withMap (extQAt cs
    Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext ((z, a.1), a.2) τ w) (Err.cap 128
    (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc ((groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
    (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
    219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num) ((1 :
    Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dTwo))) (faLay cs lo gs
    kb hM hZ
    keep n num A₀ w₀ w₁ Gd seat (namesOf cs lo (stageOf gs 219) radFull kb hM hZ no) L smpD σ₀ st₀
      e₀ (fun b : S1 × F.E.Str => mWRaw cs lo (memMain lo) (stageOf gs 219) radFull (fun i => layAt
      (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true)
      (strsOf F b.2) tree skip aF) z) a a' → ∀ w, relAt (meansQ (Fr := F) Nu Mg
    fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w → CarriedAt (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) (namesOf cs lo (stageOf gs 219) radFull kb hM hZ no) keep (SbV (groupLayK cs
        lo (stageOf gs 219) radFull kb hM hZ) B) (slV
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)
    (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ) n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L (faLay cs
    lo
    gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat (namesOf cs lo (stageOf gs 219) radFull kb hM hZ no) L
      smpD σ₀ st₀ e₀ (fun b : S1 × F.E.Str => mWRaw cs lo (memMain lo) (stageOf gs 219) radFull (fun
      i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 =
      true) (strsOf F b.2) tree skip aF) z a) (rdBK a'.1).1.rows := by
  intro z a a' hx _ hEnd w hw
  obtain ⟨hStep, hIn, hSe, hFi, hMk, hBl, hGf⟩ := hFront z a hx
  have hE := hEnd
  obtain ⟨⟨τ, -, -, hcf⟩, ew, -⟩ := hE
  obtain ⟨hH, hBook⟩ := hDoor z a a' _ _ hx hcf ew
  obtain ⟨⟨hm, hγ, hk, hh⟩, hFr⟩ :=
    behind_of_close hcf (hShp z a hx) hLA gs hle hGf Z m hH hBook
  obtain ⟨Gr, hG⟩ := closeFrame_group hcf
  have H := hShp z a hx Gr hG
  obtain ⟨hLm, hLk, hA⟩ := layout_behind hcf hG H hLA
  obtain ⟨Ly, mk, -, -, hmk, hfr⟩ := closeFrame_reads hcf
  have hfL := hMk mk hmk
  have hfr' : a'.1.live.frame.rows.fresh = mk := hfr
  have hin : ∀ j sh, ((rdK a.1).2.2.oracles[j]?).map (fun o : OnBytes.Oracle => o.shape) = some sh →
      j < a.1.book.place.size := fun j sh e => by
    obtain ⟨xo, x1, -⟩ := Option.map_eq_some_iff.1 e
    rw [hStep]
    exact (Array.getElem?_eq_some_iff.1 x1).1
  have hfo : mk < a.1.book.place.size := by
    obtain ⟨-, -, -, -, o, ho, -⟩ := sizes_at_stage hcf gs 219 hle hGf
    have ho' : (rdBK a'.1).2.oracles[mk]? = some o := by
      rw [← hfr]
      exact ho
    exact hin mk o.shape (by rw [← shape_behind hcf mk, ho']; rfl)
  have htB : tree < base := by
    unfold VerifiableInference.Desc.K12.Door.placesBelowB at hBl
    have hmem : (tree, tnF) ∈ Lp.places.take a.1.book.place.size := by
      refine List.mem_of_getElem? (i := mk) ?_
      rw [List.getElem?_take_of_lt hfo]
      exact hfL
    exact of_decide_eq_true (List.all_eq_true.1 hBl _ hmem)
  have hPB : ∀ b : {i // memMain lo i},
      planPubB Gd a.1 Lp (no b.1) (seat b.1) (aOf cs (lo.get b.1).1) = true := fun b => by
    rw [planPubB_eq, hPC b, Bool.and_true, decide_eq_true_eq]
    exact hin _ _ (H.shape b.1 (mem_members.2 b.2))
  exact hCar_end cs lo (stageOf gs 219) radFull kb hM hZ Gd seat no keep _ n num fx1 A₀ _ _ w₀ w₁ L
    smpD σ₀ st₀ e₀ Z lay m z a a' w D hW _ _ _ Pr b base _ _ tree tnF skip aF hEnd
    (hTie ((z, a'.1), a'.2) w hw) hr hH hgood H hLm hLk hA hm hγ hk hh hord hS
    (hSh_of_cf Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) (z, a.1) (strsOf F a.2) (hCfX z a hx))
    Lp hPB hPl (fun b => Nat.lt_of_lt_of_le (hsB b.1) hbD) hsB hIn hSe hFi hpos
    (by rw [hfr']; exact hfo) (by rw [hfr']; exact hfL) shF0 hfs hfa (Nat.lt_of_lt_of_le htB hbD)
    htB hfskip hFr (h2 z a hx)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.hCar_heavy
