-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FoldLaw.lean: the plain fold of the proximity test, read in the field.

The proximity test (the kind K12 of Johnson/Desc/Block.lean) folds by the functions `heard`,
`rounds` and `foldD` of Johnson/Desc/First/Close/Closing.lean. This file says what a yes of these
functions means where the rounds that they are shown are written rounds of the library's chain of
fold, code switch and base case (OnBytes/Slice/ManyDefs.lean). Statements and proofs.
Main names:
  `rounds_sem`: `rounds` on the view of k written rounds "FOLD round": its claim and its elements,
    read in the field, are the library's running claim (`claimF`) and drawn point (`ptF`).
  `foldD_sem`: a yes of `foldD`, in both of its arms, on the view of a fold's written rounds: what
    it returns, read in the field (`stmS`), is the chain's claim behind the fold (`foldNext` at the
    row read in the field, `stmG`); with what the yes holds beside: the mask's number, the records
    between, the three public tests.
Limits: No test on the words is needed, because the rounds are written rounds as shown: on every
triple x the part's `E.ofTriple x`, read by `readE`, is `toE x` (`readE_ofTriple`, without a bound).
No position is read in a fold. The written rounds dE and dT are free records here: nothing ties them
to the entries (that is the matter of `Chain.Pub`). Whether the arm in which the fold's own first
message brings the mask can be met by a written round is not shown here. Where Closing.lean and the
plain ground call the description's own tests and makers, the proofs go back to the names of the
program `verify-on-bytes` by theorems of agreement, each an equation at all arguments:
`treesMade_eq` (Johnson/Desc/Own/TreesAgree.lean) and `foldShapeFits_agrees`, `foldMaskFits_agrees`,
`foldRowFits_agrees` (Johnson/Desc/Own/FoldAgree.lean); the statements still speak of `foldShapeOk`,
`foldMaskOk` and `foldRowOk`. No statement and no proof of this file reaches a routine that runs in
a context of `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.First.Close.Closing
import Johnson.Desc.Block
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.Own.FoldAgree
import OnBytes.Slice.BlkProxFold
import OnBytes.Slice.ManyDefs

set_option autoImplicit false
namespace H2K.FoldLaw
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-! ## Yes of a chain of tests -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : First.Close.need n b = .ok u) : b = true :=
    by
  unfold First.Close.need at h
  cases b with
  | true => rfl
  | false => cases h

theorem got_ok {α : Type} {n : String} {x : Option α} {a : α} (h : got n x = .ok a) :
    x = some a := by
  unfold got at h
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- The elements that a round sends, as `heard` lays them, are in the field the library's reading of
the message. -/
theorem mapM_read : ∀ (vs : List Fmt.ItemValue) (xs : List E),
    (vs.mapM fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) = some xs →
    (vs.filterMap fun g => match g with
      | .e x => some (toE x)
      | .answer x => some (toE x)
      | _ => none) = xs.map readE
  | [], xs, h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | v :: vs, xs, h => by
    rw [List.mapM_cons] at h
    cases v with
    | e x =>
      cases hm : (vs.mapM fun v => match v with
        | .e x => some (E.ofTriple x)
        | _ => none) with
      | none => simp [hm] at h
      | some ys =>
        simp [hm] at h
        subst h
        have ih := mapM_read vs ys hm
        simp only [List.filterMap_cons, List.map_cons, ih, readE_ofTriple]
    | f x => simp at h
    | word x => simp at h
    | root x => simp at h
    | answer x => simp at h

/-- What a yes of `heard` holds. -/
theorem heard_ok (name : String) (items : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (roots : Nat)
    (xs : List E) (x : E) (h : heard name items e r roots = .ok (xs, x)) :
    (r.vals.mapM fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) = some xs ∧ ∃ t, r.drawn.elems = [t] ∧ x = E.ofTriple t := by
  unfold heard at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨ys, h6, h⟩ := bind_ok h
  have h6' := got_ok h6
  split at h
  · rename_i t ht
    cases h
    exact ⟨h6', t, ht, rfl⟩
  · cases h

/-- `heard` on a written round as a view shows it. -/
theorem heard_sem (name : String) (items : Nat) (e : Fmt.Entry) (roots : Nat) (d : PQ.RD)
    (m : (wRound d).Msg) (ch : (wRound d).Chal) (xs : List E) (x : E)
    (h : heard name items e
      (noDigest ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) ch)⟩) roots = .ok (xs, x)) :
    (∀ i, sentAt d m i = (xs.map readE).getD i 0) ∧ gOne _ (valsOf d ch) = readE x := by
  obtain ⟨h1, t, h2, rfl⟩ := heard_ok _ _ _ _ _ _ _ h
  refine ⟨fun i => ?_, ?_⟩
  · exact congrArg (fun l => l.getD i 0) (mapM_read _ _ h1)
  · rw [readE_ofTriple]
    exact gOne_of_els d m ch h2

/-! ## The rounds -/

theorem rounds_sem (dT : PQ.RD) : ∀ (k : ℕ) (es : List Fmt.Entry) (claim : E)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))) (gs : List E) (cl : E),
    rounds es ((PQ.rvSL (ckP .two) (List.replicate k dT) τ).map noDigest) claim = .ok (gs, cl) →
    readE cl = claimF dT k (readE claim) τ ∧ readP k gs = ptF dT k τ ∧ gs.length = k
  | 0, es, claim, τ, gs, cl, h => by
    cases es with
    | nil =>
      have h' : (Except.ok ([], claim) : Except String (List E × E)) = .ok (gs, cl) := h
      cases h'
      exact ⟨rfl, funext fun i => i.elim0, rfl⟩
    | cons e es =>
      have h' : (Except.error "K10.stretch" : Except String (List E × E)) = .ok (gs, cl) := h
      cases h'
  | k + 1, es, claim, (m, ch, τ), gs, cl, h => by
    cases es with
    | nil =>
      have h' : (Except.error "K10.stretch" : Except String (List E × E)) = .ok (gs, cl) := h
      cases h'
    | cons e es =>
      have h0 : rounds (e :: es)
          (noDigest ⟨PQ.PlainOf.gots dT.items (GPlain.old (b := dT.entry.work) m.2),
            (ckP .two).dr dT.entry dT.kind (GChal.old (b := dT.entry.work) ch)⟩ ::
            (PQ.rvSL (ckP .two) (List.replicate k dT) τ).map noDigest) claim = .ok (gs, cl) := h
      rw [rounds] at h0
      obtain ⟨⟨xs, g⟩, h1, h0⟩ := bind_ok h0
      obtain ⟨hs, hg⟩ := heard_sem _ _ _ _ dT m ch xs g h1
      split at h0
      · rename_i c0 c2 g' heq
        cases heq
        obtain ⟨⟨gs', cl'⟩, h2, h0⟩ := bind_ok h0
        cases h0
        obtain ⟨i1, i2, i3⟩ := rounds_sem dT k es _ τ gs' cl' h2
        have hs0 : sentAt dT m 0 = readE c0 := hs 0
        have hs1 : sentAt dT m 1 = readE c2 := hs 1
        refine ⟨?_, ?_, congrArg (· + 1) i3⟩
        · rw [i1, readE_foldClaimRound, ← hs0, ← hs1, ← hg]
          rfl
        · funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact hg.symm
          · exact congrFun i2 j
      · cases h0

/-! ## The fold -/

theorem spend_codes {L : Type} (d d' : _root_.Desc.Plain.DState L) (o : Nat)
    (h : Ground.spendAsMaskP d o = some d') : d'.st.codes = d.st.codes := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h; rfl
  · cases h

theorem recv_codes {L : Type} (firstTree : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat)
    (h : Ground.recvP firstTree d sent = some (ids, d')) : d'.st.codes = d.st.codes := by
  unfold Ground.recvP at h
  split at h
  · rw [Own.treesMade_eq] at h
    cases hl : layTrees d.st.codes sent with
    | none => rw [hl] at h; cases h
    | some lay => rw [hl] at h; cases h; rfl
  · cases h

/-- A yes of the plain fold on the view of a fold's written rounds (shown without the sealed digest,
as Block.step shows them). -/
theorem foldD_sem {L : Type} (s : Sg) (F : FoldShape) (hk : F.layout.k = s.h + s.g)
    (hh : F.layout.h = s.h) (firstTree : Nat) (d d' : _root_.Desc.Plain.DState L) (row : GroupRow)
    (mask : Option Nat) (es : List Fmt.Entry) (dE dT : PQ.RD)
    (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (out : SingleRows)
    (hZ : (d.st.codes.mask.getD F.maskCode default).ell = s.Z.l)
    (h : foldD firstTree d F row mask es
      ((PQ.rvSL (ckP .two) (foldRds s dE dT) τ).map noDigest) = .ok (out, d')) :
    stmS s out = foldNext s s.Z.l dE dT (stmG s row) τ ∧
    ∃ (id : Nat) (d1 : _root_.Desc.Plain.DState L) (eps claim : E) (gamma : List E),
      ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
        Ground.recvP firstTree d #[foldMaskNotice F] = some (ids, d1) ∧ ids[0]? = some id)) ∧
      Ground.spendAsMaskP d1 id = some d' ∧ out = foldOutput d'.st F row id eps gamma claim ∧
      readP (s.h + s.g) gamma = foldPt s dE dT τ ∧ gamma.length = s.h + s.g ∧
      foldShapeOk d.st F = true ∧ foldMaskOk d1.st F id = true ∧
      foldRowOk d'.st F row = true := by
  obtain ⟨m, ch, τ⟩ := τ
  cases es with
  | nil => cases h
  | cons eE eR =>
    have h0 : foldD firstTree d F row mask (eE :: eR)
        (noDigest ⟨PQ.PlainOf.gots dE.items (GPlain.old (b := dE.entry.work) m.2),
          (ckP .two).dr dE.entry dE.kind (GChal.old (b := dE.entry.work) ch)⟩ ::
          (PQ.rvSL (ckP .two) (List.replicate (s.h + s.g) dT) τ).map noDigest) = .ok (out, d') := h
    rw [foldD] at h0
    obtain ⟨_, _, h0⟩ := bind_ok h0
    obtain ⟨_, _, h0⟩ := bind_ok h0
    obtain ⟨_, hshape, h0⟩ := bind_ok h0
    have h1 : ∃ (id : Nat) (d1 : _root_.Desc.Plain.DState L),
        ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
          Ground.recvP firstTree d #[foldMaskNotice F] = some (ids, d1) ∧ ids[0]? = some id)) ∧
        (do
          First.Close.need "K10.maskfits" (Own.foldMaskFits d1.st F id)
          First.Close.named (Ground.spendAsMaskL d1.st id)
          let d2 ← got "K10.maskfits" (Ground.spendAsMaskP d1 id)
          match ← heard "FOLD epsilon" 1 eE
              (noDigest ⟨PQ.PlainOf.gots dE.items (GPlain.old (b := dE.entry.work) m.2),
                (ckP .two).dr dE.entry dE.kind (GChal.old (b := dE.entry.work) ch)⟩)
              (d1.roots - d.roots) with
          | ([sum], eps) =>
            First.Close.need "K10.rowfits" (Own.foldRowFits d2.st F row)
            let (gamma, claim) ← rounds eR
              ((PQ.rvSL (ckP .two) (List.replicate (s.h + s.g) dT) τ).map noDigest)
              (maddE sum eps row.target)
            pure (foldOutput d2.st F row id eps gamma claim, d2)
          | _ => .error "K10.items") = Except.ok (out, d') := by
      cases mask with
      | some o => exact ⟨o, d, .inl ⟨rfl, rfl⟩, h0⟩
      | none =>
        obtain ⟨_, _, h0⟩ := bind_ok h0
        obtain ⟨⟨ids, dd⟩, hr, h0⟩ := bind_ok h0
        obtain ⟨i0, hi, h0⟩ := bind_ok h0
        exact ⟨i0, dd, .inr ⟨rfl, ids, got_ok hr, got_ok hi⟩, h0⟩
    obtain ⟨id, d1, hcase, h0⟩ := h1
    obtain ⟨_, hmask, h0⟩ := bind_ok h0
    obtain ⟨_, _, h0⟩ := bind_ok h0
    obtain ⟨d2, hsp, h0⟩ := bind_ok h0
    obtain ⟨⟨xs, eps⟩, hh1, h0⟩ := bind_ok h0
    have hsp' := got_ok hsp
    obtain ⟨hs, hg⟩ := heard_sem _ _ _ _ dE m ch xs eps hh1
    have hc1 : d1.st.codes = d.st.codes := by
      rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
      · rfl
      · exact recv_codes _ _ _ _ _ hr
    split at h0
    · rename_i sum eps' heq
      cases heq
      obtain ⟨_, hrow, h0⟩ := bind_ok h0
      obtain ⟨⟨gamma, claim⟩, hr, h0⟩ := bind_ok h0
      cases h0
      obtain ⟨i1, i2, i3⟩ := rounds_sem dT (s.h + s.g) eR _ τ gamma claim hr
      have hrow' := (Own.foldRowFits_agrees _ _ _).trans (need_ok hrow)
      have hvec := vecS_foldOutput_fits s d'.st F row id eps gamma claim hk hh i3 hrow'
        (by rw [spend_codes _ _ _ hsp', hc1]; exact hZ)
      have hs0 : sentAt dE m 0 = readE sum := hs 0
      refine ⟨Prod.ext ?_ ?_, id, d1, eps, claim, gamma, hcase, hsp', rfl, i2, i3,
        (Own.foldShapeFits_agrees _ _).trans (need_ok hshape),
        (Own.foldMaskFits_agrees _ _ _).trans (need_ok hmask), hrow'⟩
      · show readE claim = _
        rw [i1, readE_maddE, ← hs0, ← hg, mul_comm]
        rfl
      · show vecS s (foldOutput d'.st F row id eps gamma claim) = _
        rw [hvec, ← hg, i2]
        rfl
    · cases h0

end H2K.FoldLaw
