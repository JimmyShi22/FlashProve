-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawTable.lean: THE LAW OF THE SMALLNESS TEST'S DRAW AT ANY TWO TABLES OF
CELLS.

The law `k08_row` (Johnson/Desc/First/K8/LawRow.lean) reads its cells through a layout of committed
entries Y over a finite index set: `Y.cellAt (entW w) t r c`. It spends of Y nothing but that
reading. The table of joints' sentences read their cells through a table (array, row, column) ↦
field element that is given outright. So here the same law stands at two such tables, given
outright:
  entE: from the members' messages; entW: from the witness;
  hE: at every EARLY cell (an array that the drawn matrix multiplies) the two agree.
  `symT`, `u3T`, `digT`, `tabReads`, `tab_atT`, `tab_onA`, `tab_keepsW`, `tab_relB_of_rows`,
  `tieT_of_relIn`, `tieT_of_relA`: LawLay.lean's and LawTie.lean's, at tables.
  `k08_rowT`: **the row of the block of the draw**: in front: the pins and the tie (`TieAt entW`);
    behind: the pins, the forms of the run "small" (`SmallAt entW`) and the digits (`DigitsAt
    entW`).
  `k08_rowT_cap`: at 128 combinations, at the least error: at most 2 ^ -128 a round.
  `k08_rowT_named`: with the members, their seats, the book's inverse and the base as functions with
    code.
HOW IT WAS MADE: the five proofs are those of the files named, with `Y.cellAt (ent x)` replaced by
`ent x` and the lemma on equal cells by hE itself: by program, then through Lean. The elder law is
this one at entE x := `Y.cellAt` of the elder's, and stays as it lies.
Limits. Those of LawRow.lean. Nothing on soundness of any verifier.

-/
import Johnson.Desc.First.K8.LawNamedRow
import Johnson.Desc.First.K8.LawRowCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable (tl0 : HTailF2)

def symT {M : Type} (ent : M → ℕ → ℕ → ℕ → Cb.Gl.E) (m : M) (μ i' c : ℕ) : Cb.Gl.E :=
  ent m (tl0.gtTree.getD μ 0) i' c

def u3T {M : Type} (ent : M → ℕ → ℕ → ℕ → Cb.Gl.E) (m : M) (pos : ℕ) : Cb.Gl.E :=
  ent m (u3Of tl0) 0 pos

def digT {W : Type} (ent : W → ℕ → ℕ → ℕ → Cb.Gl.E) (w : W) :
    Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0).size :=
  ⟨fun μ u i => ent w tl0.ix.ZZ u ((tl0.zzCol μ 0 0).getD 0 + i),
    fun μ u i => ent w tl0.ix.ZZ u ((tl0.zzCol μ 1 0).getD 0 + i)⟩

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ)
  (arr : ℕ → ℕ → ℕ) {Cells Tok : Type} (entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E)

theorem tab_atT
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (tl : HTailF2) (hp : SamePub tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) (hβ : tl.cfF = listOf β)
    (w : Wit Cells Tok MsgT) :
    AtT Reading.gl tl (OnBytes.Tie.Pv.Tail.sizeOf tl0)
      (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symT tl0 entE) (u3T tl0 entE)
        (digT tl0 entW))
      (blank tl) (msgsOf cs l seat' arr w) (digT tl0 entW w) β
      (entW w) where
  phi := fun n Fn hn j _ => by
    show phiAt Reading.gl (blank tl) n j = _
    unfold phiAt
    have e : (blank tl).funs.getD n default = Fn := by
      show tl.funs.getD n default = Fn
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn]
      rfl
    rw [e]
  sym := fun μ i' c hμ _ _ => by
    show entE _ (tl0.gtTree.getD μ 0) i' c = entW w (tl.gtTree.getD μ 0) i' c
    rw [hp.gt]
    exact hE w _ _ _ (early_sym (Nat.lt_of_lt_of_le (hp.nm ▸ hμ) hgt) i' c)
  u3 := fun y _ d _ => by
    show entE _ (u3Of tl0) 0 _ = entW w (u3Of tl) 0 _
    have e : u3Of tl = u3Of tl0 := by
      unfold u3Of
      rw [hp.ix]
    rw [e]
    exact hE w _ _ _ (early_u3 hu _ _)
  zl := fun μ u i => by
    show entW w tl0.ix.ZZ u ((tl0.zzCol μ 0 0).getD 0 + i) =
      entW w tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)
    rw [hp.ix, zzCol_same hp]
  zh := fun μ u i => by
    show entW w tl0.ix.ZZ u ((tl0.zzCol μ 1 0).getD 0 + i) =
      entW w tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i)
    rw [hp.ix, zzCol_same hp]
  th := fun μ u c => by
    have h := th_draw (K := Cb.Gl.E) tl (sizeOf_same hp.toSameSize) hnm hfirst β μ u c
    rw [← hβ] at h
    exact h

variable {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

def tabReads : Reads Cl (Wit Cells Tok MsgT) F atS p base e
    (callerAtRecord tl0
      (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symT tl0 entE) (u3T tl0 entE)
        (digT tl0 entW))
      (sigOf cs l) id (fun x => SameLay x.1 tl0)) :=
  frameReads G cs l seat' arr tl0
    (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symT tl0 entE) (u3T tl0 entE)
      (digT tl0 entW))
    id (fun x => SameLay x.1 tl0) (recOf tl0) () smpOf id (recOf_put tl0) hs Cl F p base e hseat

theorem tab_onA (a : S × F.E.Str) :
    (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onA a ↔
      (sigOf cs l).CF (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) ∧
        SameLay (recOf tl0 a.1) tl0 :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩

theorem tab_keepsW (hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onA
      (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onB
      (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA
      (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relB
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err :=
  hear_keepsW _ hf (OnBytes.Tie.Pv.Tail.sizeOf_ok tl0) he

theorem tab_relB_of_rows
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (recOf tl0 a.1) tl0) (hz : SameSize tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) (hβ : tl.cfF = listOf β)
    (hdec : ∀ i, (sigOf cs l).decs (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) i =
      some (msgsOf cs l seat' arr w i))
    (pc : Nat) (hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ u i,
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.lo ((digT tl0 entW w).zl μ u i) ∧
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.hi ((digT tl0 entW w).zh μ u i))
    (hrows : ∀ r ∈ rowsTail Reading.gl tl tl.funs pc,
      r.2 (entW w) = 0) :
    (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relB a w := by
  have hx : recOf tl0 a.1 = blank tl := by
    unfold recOf
    rw [ht]
    rfl
  have hp : SamePub tl tl0 := by
    rw [hx] at hp0
    exact { toSameSize := hz, toSameLay := ⟨hp0.gt, hp0.ix, hp0.mz, hp0.off⟩ }
  have hcf : (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).cf a.1 =
      listOf β := by
    show (a.1.tl?.map (·.cfF)).getD #[] = _
    rw [ht]
    exact hβ
  have ho := relOut_cut tl (sizeOf_same hz) pc
    (tab_atT tl0 cs l seat' arr entE entW hE tl hp hgt hu hnm hfirst β hβ w) hfit htree hdig hrows
  rw [← hx] at ho
  exact Reads.relB_of_relOut _ a w β hcf hdec trivial ho

end
section
variable (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E)

theorem tieT_of_relIn
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (tl : HTailF2) (hp : SamePub tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (w : Wit Cells Tok MsgT)
    (h : relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symT tl0 entE)
      (u3T tl0 entE) (digT tl0 entW)).letters (blank tl) (msgsOf cs l seat' arr w)) :
    TieOf tl fun a r c => entW w a r c := by
  obtain ⟨b, h1, h2, h3⟩ := reads_of_relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT)
    (symT tl0 entE) (u3T tl0 entE) (digT tl0 entW)) h
  have hU : u3Of tl = u3Of tl0 := by
    unfold u3Of
    rw [hp.ix]
  refine ⟨fun μ i c => b μ c i, ?_, ?_, ?_⟩
  · intro μ hμ c hc i hi
    rw [hp.nm] at hμ
    rw [hp.k] at hc
    rw [hp.m] at hi
    exact h1 μ hμ c hc i hi
  · intro μ hμ c hc i' hi'
    rw [hp.nm] at hμ
    rw [hp.k] at hc
    rw [hp.m] at hi'
    rw [hp.gt, pack_congr (hp.m μ)]
    refine Eq.trans ?_ (h2 μ hμ c hc i' hi')
    exact (hE w _ _ _ (early_sym (Nat.lt_of_lt_of_le hμ hgt) i' c)).symm
  · intro n Fn hn c sg pos hpos
    obtain ⟨g1, g2, g3, rfl⟩ := tabAt_some tl hpos
    have hT : (OnBytes.Tie.Pv.Tail.sizeOf tl0).tabs[n]? = some ⟨Fn.mat, Fn.len, Fn.start⟩ := by
      have ht := hp.tabs
      unfold SameShapes at ht
      show (tl0.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))[n]? = _
      rw [← ht, List.getElem?_map, Array.getElem?_toList, hn]
      rfl
    have hφ : ∀ j, phiAt Reading.gl (blank tl) n j = Reading.gl.val (Fn.phi.getD j zeroE) := by
      intro j
      unfold phiAt
      have e : (blank tl).funs.getD n default = Fn := by
        show tl.funs.getD n default = Fn
        rw [Array.getD_eq_getD_getElem?, hn]
        rfl
      rw [e]
    rw [hp.nm] at g1
    rw [hp.k] at g2
    rw [hp.m] at g3
    have h4 := h3 n ⟨Fn.mat, Fn.len, Fn.start⟩ hT g1 c g2 sg g3
    rw [hU, hp.m]
    refine Eq.trans ?_ (h4.trans (Finset.sum_congr rfl fun j _ => ?_))
    · exact (hE w _ _ _ (early_u3 hu _ _)).symm
    · show phiAt Reading.gl (blank tl) n j * _ = _
      rw [hφ j]

variable {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

theorem tieT_of_relA
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (recOf tl0 a.1) tl0) (hz : SameSize tl tl0)
    (h : (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA a w) :
    TieAt entW a.1 w := by
  have hx : recOf tl0 a.1 = blank tl := by
    unfold recOf
    rw [ht]
    rfl
  have hp : SamePub tl tl0 := by
    rw [hx] at hp0
    exact { toSameSize := hz, toSameLay := ⟨hp0.gt, hp0.ix, hp0.mz, hp0.off⟩ }
  have h' : relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symT tl0 entE)
      (u3T tl0 entE) (digT tl0 entW)).letters (recOf tl0 a.1) (msgsOf cs l seat' arr w) :=
    h.2.2
  rw [hx] at h'
  exact ⟨tl, ht, tieT_of_relIn tl0 cs l seat' arr entE entW hE tl hp hgt hu w h'⟩

end
section
variable (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
  (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

local notation "LR" => tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat

theorem k08_rowT
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (fun a => (LR).onA a ∧ Extra a.1) (fun b => (LR).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧
        TieAt entW a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧
        SmallAt entW b.1 w ∧
        DigitsAt entW b.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err := by
  have hf := fits_of_place hP
  refine Iop.Reduction.Leads.conseq
    (tab_keepsW tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hf he)
    (fun _ h => h.1) fun a τ b ha hout hq => ?_
  obtain ⟨m, c, ⟨⟩⟩ := τ
  obtain ⟨_, ⟨cols, k, hstep⟩, _⟩ := piece_out atS p base e a b m c hout
  obtain ⟨_, _, _, c4, c5, _, _, _, hl, _⟩ :=
    (hear_law_view (Cl := Cl) hf atS m c F.ft a.1 b.1 k cols).1 hstep
  obtain ⟨tl, ht, hb⟩ := atS_lay a.1 b.1 _ _ hl
  have hd : tl.NM = p.ks.length := by simpa [atS, ht] using c4
  have hk : tl.mats.toList.map (·.k) = p.ks := by simpa [atS, ht] using c5
  have hnm : tl.NM = tl.mats.size := by rw [hd, ← hk]; simp
  rw [firstColumns_of_tests tl p hk] at hb
  have htb : b.1.tl? = some { tl with
      cfF := listOf (matrixOf hf c)
      cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } := by
    rw [hb]
    exact putTl_tl a.1 tl _ ht
  have hz : SameSize tl tl0 :=
    sameSize_of_place (placeRec_of_yes (Cl := Cl) p tl F.ft a.1 b.1 k _ cols ht hstep) hP
  have hpa : SameLay (recOf tl0 a.1) tl0 :=
    ((tab_onA tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat a).1 ha.1).2
  have hpb : SameLay (recOf tl0 b.1) tl0 := by
    rw [hb, recOf_put tl0 a.1 tl _ _ ht]
    exact hpa
  obtain ⟨hfit, htree⟩ := ha.2 tl ht
  refine ⟨⟨hq.1, fun t' ht' => ?_⟩, fun w hw => ?_⟩
  · obtain rfl := Option.some.inj (htb.symm.trans ht')
    exact ⟨hfit.of_same rfl rfl rfl, htree⟩
  · obtain ⟨hpin, ⟨t1, e1, hrows⟩, ⟨t2, e2, hdg⟩⟩ := hw
    obtain rfl := Option.some.inj (htb.symm.trans e1)
    obtain rfl := Option.some.inj (htb.symm.trans e2)
    have hx : recOf tl0 a.1 = blank tl := by
      unfold recOf
      rw [ht]
      rfl
    have hp : SamePub tl tl0 := by
      have h0 := hpa
      rw [hx] at h0
      exact { toSameSize := hz, toSameLay := ⟨h0.gt, h0.ix, h0.mz, h0.off⟩ }
    have hB := tab_relB_of_rows tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hE b
      w _ htb hpb ⟨hz.nm, hz.m, hz.k, hz.tau, hz.tabs⟩ hgt hu hnm rfl (matrixOf hf c) rfl hpin 0
      (hfit.of_same rfl rfl rfl) htree
      (fun μ u i => by
        have h1 := hdg μ.val (by show μ.val < tl.NM; rw [hp.nm]; exact μ.isLt) u.val
          (by show u.val < tl.tau; rw [hp.tau]; exact u.isLt) i.val
          (by show i.val < (tl.mats.getD μ.val {}).m; rw [hp.m]; exact i.isLt)
        have z0 : tl.zzCol μ.val 0 0 = tl0.zzCol μ.val 0 0 := zzCol_same hp _ _ _
        have z1 : tl.zzCol μ.val 1 0 = tl0.zzCol μ.val 1 0 := zzCol_same hp _ _ _
        have h2 : Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.lo
              (entW w tl.ix.ZZ u.val ((tl.zzCol μ.val 0 0).getD 0 + i.val)) ∧
            Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.hi
              (entW w tl.ix.ZZ u.val ((tl.zzCol μ.val 1 0).getD 0 + i.val)) := h1
        rw [hp.ix, z0, z1] at h2
        exact h2) hrows
    have hA := hq.2 w hB
    exact ⟨hA.1, tieT_of_relA tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hE hgt hu
      a w tl ht hpa hz hA⟩
end

theorem k08_rowT_cap (tl0 : HTailF2) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    {Cells Tok : Type} (entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
    (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
    (smpOf : S → (sigOf cs l).Smp)
    (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
      smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
    (Cl : Type) (F : Frame) (p : Par) (base : ℕ) (hseat : ∀ i, (seat' i).1 < base)
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0) (hτ : p.tau = 128) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).ior.red.KeepsW
      (fun a => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onA a ∧ Extra a.1)
      (fun b => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧
        TieAt entW a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧
        SmallAt entW b.1 w ∧
        DigitsAt entW b.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).err ∧
    Err.Below (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).err ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨k08_rowT tl0 cs l seat' arr entE entW G smpOf hs Cl F p base _ hseat hE hgt hu hP
      (Nat.le_refl _),
    piece_err_cap atS p base (fits_of_place hP) hτ⟩

section
variable (tl0 : HTailF2) (cs : OnBytes.Codes)
  (rad : OracleShape → Nat) (S₀ : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx)

variable {Cells Tok : Type}
  (entE : (sigOf cs (Named.listOf rad S₀ book tl L)).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
  (smpOf : S → (sigOf cs (Named.listOf rad S₀ book tl L)).Smp)
  (hs : ∀ (s : S) (t : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some t →
    smpOf (s.putTl { t with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (e : ℕ)
  {seat : Seat G.S₁} {b : Block G.S₁ G.Cl} (hb : LikeP seat p b) (pre post : List (Block G.S₁ G.Cl))
  (hflat : G.first.blocksInOrder = pre ++ b :: post) (hG : G.planOk = true)
  (hN : Named.namedB p S₀ book tl L = true)

include smpOf hs hb hflat hG hN in
theorem k08_rowT_named
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs (Named.listOf rad S₀ book tl L) (Named.seatFn rad S₀ book tl L)
        (Named.arrOf book) w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).ior.red.KeepsW
      (fun a => (tabReads tl0 cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN)).onA a ∧ Extra a.1)
      (fun c => (tabReads tl0 cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN)).onB c ∧ Extra c.1)
      (fun a w => PinsAt cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) G smpOf F a w ∧
        TieAt entW a.1 w)
      (fun c w => PinsAt cs (Named.listOf rad S₀ book tl L)
          (Named.seatFn rad S₀ book tl L) (Named.arrOf book) G smpOf F c w ∧
        SmallAt entW c.1 w ∧
        DigitsAt entW c.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).err :=
  k08_rowT tl0 cs (Named.listOf rad S₀ book tl L)
      (Named.seatFn rad S₀ book tl L) (Named.arrOf book) entE entW G smpOf hs Cl F p _ e
    (named_seats_below_P G hb pre post hflat hG rad S₀ book tl L hN) hE hgt hu hP he

end
end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.tab_atT
#print axioms VerifiableInference.Desc.First.K8.tieT_of_relA
#print axioms VerifiableInference.Desc.First.K8.k08_rowT
#print axioms VerifiableInference.Desc.First.K8.k08_rowT_cap
#print axioms VerifiableInference.Desc.First.K8.k08_rowT_named
