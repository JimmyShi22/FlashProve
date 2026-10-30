-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointGood.lean: **"LIN point" in the form of the rule of composition**, at the
shared chain's own first block: the last of the eight.

Behind the block stands the first border of the table (Johnson/Desc/K14/Law/BordersU.lean): of the
message to come: near, RecAll, DotU. In front of it: the stored table decodes (Dec), and the other
vector IS the row weights applied to the matrix that it decodes to (VIs).
The lost points are of two sorts, as in the library's link at that place (Cb/Ld/LdLin.lean: errPt):
  the key's       gamma, the point's high part, is bad for the stored table and its record: some
                  vector is near the fold at gamma and meets the record's row there, and yet its
                  message is not the fold of what the table holds. HERE A LETTER, BadKey, with two
                  premises: no more than ef points gamma are bad (hkey); at a gamma that is not bad,
                  near and RecAll give that the table decodes and that the message is the fold of
                  the rows that it decodes to (hgood).
  the slot's      the other vector is not the row weights applied to the matrix, and yet (Dot)'s
                  equation holds at the point: no more than kCol |K| ^ (kCol - 1) points.
  linPoint_inv    what a yes of "LIN point" notes.
  gamOf, loOf, drop_ofFn, take_ofFn, cnt_high   the point's two parts; a property of the high part
                  holds of |K| ^ kLo points for each gamma of which it holds.
  dotTrue_of      near's and RecAll's fruit with DotU: (Dot)'s equation with the matrix itself.
  VIs             the claim in front.
  point_goodIn    **the law**, at ef |K| ^ kLo + kCol |K| ^ (kCol - 1).

What is not claimed. BadKey, Dec and Tab (what the stored table decodes to) are letters; hkey and
hgood are premises: the first is the statement on codes', the second a tie to the library's typed
notions that is not typed here. Premises beside them: the written round draws kCol elements and no
position; UNDER THE PROMISE IN FRONT (Prm) ALONE: at a yes the pin goes back and the next border's
letter Prm' holds behind; two pinned witnesses have the same other vector. g, wv, Pin, Prm, Prm' are
letters. ONE statement: for a batch the slot's sort is counted
once a slot. No member is shown. A block that refuses all has GoodIn too. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.BordersU
import Johnson.Desc.K14.Law.OmegaTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

/-- A new group leaves the small record, the messages and the codes. -/
theorem newGroupP_same (d d' : St) (c mc n : Nat) (h : newGroupP d c mc = some (n, d')) :
    d'.loc = d.loc ∧ d'.st.oracles = d.st.oracles ∧ d'.st.codes = d.st.codes := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- What a yes of "LIN point" notes: one round; the point drawn; the key and the statement's
messages and codes stay. -/
theorem linPoint_inv (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    ∃ r, rs = [r] ∧ d'.loc.psiSh = drawn r ∧ d'.loc.key = d.loc.key ∧
      d'.st.oracles = d.st.oracles ∧ d'.st.codes = d.st.codes := by
  unfold linPoint at h
  split at h
  · rename_i r
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    obtain ⟨l1, o1, c1⟩ := newGroupP_same d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      obtain ⟨l2, o2, c2⟩ := newGroupP_same d1 d2 _ _ gO h3
      exact ⟨r, rfl, rfl, by show d2.loc.key = _; rw [l2, l1], o2.trans o1, c2.trans c1⟩
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      exact ⟨r, rfl, rfl, by show d1.loc.key = _; rw [l1], o1, c1⟩
  · cases h

variable {K : Type}

/-- The point's high part. -/
def gamOf (kLo v : Nat) (psi : Fin (kLo + v) → K) : Fin v → K :=
  fun i => psi ⟨kLo + i.val, Nat.add_lt_add_left i.isLt kLo⟩

/-- The point's low part. -/
def loOf (kLo v : Nat) (psi : Fin (kLo + v) → K) : Fin kLo → K :=
  fun i => psi ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right kLo v)⟩

/-- The list behind the first kLo coordinates is the high part. -/
theorem drop_ofFn (kLo v : Nat) (psi : Fin (kLo + v) → K) :
    (List.ofFn psi).drop kLo = List.ofFn (gamOf kLo v psi) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [gamOf]

/-- The first kLo coordinates are the low part. -/
theorem take_ofFn (kLo v : Nat) (psi : Fin (kLo + v) → K) :
    (List.ofFn psi).take kLo = List.ofFn (loOf kLo v psi) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [loOf]

variable [Field K]

/-- A property of the high part holds of |K| ^ kLo points for each gamma of which it holds. -/
theorem cnt_high [Fintype K] (kLo v : Nat) (B : (Fin v → K) → Prop) :
    cnt (fun psi : Fin (kLo + v) → K => B (gamOf kLo v psi)) ≤ cnt B * Fintype.card K ^ kLo := by
  have hinj : Function.Injective fun psi : Fin (kLo + v) → K =>
      (gamOf kLo v psi, loOf kLo v psi) := by
    intro a b h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    funext i
    by_cases hi : i.val < kLo
    · exact congrFun h2 ⟨i.val, hi⟩
    · have hv : i.val - kLo < v := by have := i.isLt; omega
      have e := congrFun h1 ⟨i.val - kLo, hv⟩
      have ei : (⟨kLo + (i.val - kLo), Nat.add_lt_add_left hv kLo⟩ : Fin (kLo + v)) = i :=
        Fin.ext (by show kLo + (i.val - kLo) = i.val; omega)
      unfold gamOf at e
      simp only [ei] at e
      exact e
  have h := VerifiableInference.Desc.K1.cnt_comp_le _ hinj
    fun x : (Fin v → K) × (Fin kLo → K) => B x.1 ∧ True
  have h2 : cnt (fun x : (Fin v → K) × (Fin kLo → K) => B x.1 ∧ True) =
      cnt B * cnt fun _ : Fin kLo → K => True := cnt_and_prod B fun _ => True
  have hT : cnt (fun _ : Fin kLo → K => True) = Fintype.card K ^ kLo := by
    classical
    rw [cnt_eq_card_filter]
    simp
  rw [h2, hT] at h
  exact le_trans (cnt_mono fun psi hp => ⟨hp, trivial⟩) h

/-- **Near's and RecAll's fruit with DotU**: (Dot)'s equation with the matrix itself. -/
theorem dotTrue_of (R kLo v : Nat) (Tab : Nat → Nat → K) (psiLo gam : List K) (g u V : Nat → K)
    (hp : psiLo.length = kLo) (hU : UIsFold R kLo v Tab gam u)
    (hD : ∑ y ∈ Finset.range R, g y * ∑ t ∈ Finset.range (2 ^ kLo),
        eqK psiLo t * u (t + 2 ^ kLo * y) =
      ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (psiLo ++ gam) c * V c) :
    ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (psiLo ++ gam) c * V c =
      ∑ y ∈ Finset.range R, g y *
        ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (psiLo ++ gam) c * matOf kLo Tab y c := by
  rw [← hD]
  refine Finset.sum_congr rfl fun y hy => ?_
  exact congrArg (fun z => g y * z) (omegaIs_of_col R kLo v Tab psiLo gam
    (fun y => ∑ t ∈ Finset.range (2 ^ kLo), eqK psiLo t * u (t + 2 ^ kLo * y)) u hp
    (fun _ _ => rfl) hU y (Finset.mem_range.1 hy))

/-- The claim in front of "LIN point": the other vector is the row weights applied to the matrix. -/
def VIs (S : LinShape) (g : Nat → K) (Tab : Nat → Nat → K) (V : Nat → K) : Prop :=
  ∀ c < 2 ^ S.kCol, V c = ∑ y ∈ Finset.range S.matrixRows, g y * matOf S.kLo Tab y c

variable {W : Type} {F : Frame}
variable (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
  (Prm Prm' : St × F.E.Str → Prop)

/-- The first block decides by "LIN point". -/
theorem point_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ d rs gs d', b1.decide d rs gs = .ok d' → linPoint P.par d rs = some d' := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact fun d rs gs d' h => why_some h

open Classical in
/-- **"LIN point" in the form of the rule of composition.** ef: the number of bad points gamma; e: a
number that is at least ef |K| ^ kLo + kCol |K| ^ (kCol - 1). -/
theorem point_goodIn (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat) (base : Nat) (d : RDT)
    {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop) (ef e : Nat)
    (he : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e)
    (hkey : ∀ a, Prm a → cnt (BadKey a) ≤ ef)
    (hgood : ∀ (a : St × F.E.Str) (x : St) (m : Words GE) (gam : Fin P.par.S.fold.index.v → GE),
      Prm a → ¬ BadKey a gam →
      (gamma P.par.S x.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam →
      x.loc.key = a.1.loc.key → x.st.codes = a.1.st.codes →
      NearAt OnBytes.Model.Reading.gl P.par x m (tabOf a.2) e' →
      RecAll OnBytes.Model.Reading.gl P.par x m →
      Dec a ∧ UIsFold P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v (Tab a) (List.ofFn gam)
        (uOf x.loc m))
    (c1 : Carries (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e) Pin Prm Prm')
    (hdetV : ∀ (x : St × F.E.Str) w w', Prm x → Pin x w → Pin x w' → wv w = wv w') :
    (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).GoodIn
      (fun a => Prm a) (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm' a)
      (fun a w => Pin a w ∧ Dec a ∧ VIs P.par.S g (Tab a) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w))) := by
  refine goodIn_of_count _ _ _ _ _ (Fin P.par.S.kCol → GE) e
    (fun _ => (vecMaps d P.par.S.kCol).carry)
    (fun _ => (vecMaps d P.par.S.kCol).fits (vecMaps_ok hd) _)
    (fun a psi => BadKey a (gamOf P.par.S.kLo P.par.S.fold.index.v psi) ∨
      ∃ w, Pin a w ∧ ¬ VIs P.par.S g (Tab a) (wv w) ∧
        ∑ c ∈ Finset.range (2 ^ P.par.S.kCol), eqK (List.ofFn psi) c * wv w c =
          ∑ y ∈ Finset.range P.par.S.matrixRows, g y *
            ∑ c ∈ Finset.range (2 ^ P.par.S.kCol),
              eqK (List.ofFn psi) c * matOf P.par.S.kLo (Tab a) y c) ?_ ?_
  · intro a ha
    refine le_trans (cnt_or_le _ _) (le_trans (Nat.add_le_add ?_ ?_) he)
    · exact le_trans (cnt_high P.par.S.kLo P.par.S.fold.index.v (BadKey a))
        (Nat.mul_le_mul_right _ (hkey a ha))
    · by_cases hw0 : ∃ w0, Pin a w0 ∧ ¬ VIs P.par.S g (Tab a) (wv w0)
      · obtain ⟨w0, hp0, hn0⟩ := hw0
        have hgap : ∃ c < 2 ^ P.par.S.kCol, wv w0 c ≠
            ∑ y ∈ Finset.range P.par.S.matrixRows, g y * matOf P.par.S.kLo (Tab a) y c := by
          unfold VIs at hn0
          push Not at hn0
          exact hn0
        refine le_trans (cnt_mono fun psi hq => ?_) (le_trans
          (le_of_eq (@cnt_eq_card_filter _ _ _ fun _ => Classical.propDecidable _))
          (dotTrueCatches P.par.S.matrixRows P.par.S.kCol (matOf P.par.S.kLo (Tab a)) g (wv w0)
            hgap))
        obtain ⟨w, hp, _, hq⟩ := hq
        rw [hdetV a w0 w ha hp0 hp]
        exact hq
      · rw [cnt_false fun psi hq => hw0 (by obtain ⟨w, hp, hn, _⟩ := hq; exact ⟨w, hp, hn⟩)]
        exact Nat.zero_le _
  · intro a τ b ha hout
    obtain ⟨hy, gs, hdc⟩ := piece_yes _ a τ b hout
    have k1 := point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdc
    obtain ⟨r, hr, hpsi, hkeyE, hor, hco⟩ := linPoint_inv _ _ _ _ k1
    have ht := piece_tests _ a τ b hout
    simp only [sTests, Bool.and_eq_true] at ht
    have hp : (vecMaps d P.par.S.kCol).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
    obtain ⟨m, c, ⟨⟩⟩ := τ
    have hr' : [noDigest (shownAt d m c)] = [r] := hr
    obtain rfl := (List.cons.inj hr').1
    have hsh := drawn_shown hd m c
    refine ⟨_, (vecMaps d P.par.S.kCol).tr_of_pass (m, c, ()) hp, fun hnl =>
      ⟨⟨⟨a.1, hS, _, k1⟩, c1.keep a _ b ha hout⟩, fun w hw => ?_⟩⟩
    obtain ⟨⟨hpin, _, _⟩, hnear, hrec, hdot⟩ := hw
    have hpa := c1.back a _ b w ha hout hpin
    have hnb : ¬ BadKey a (gamOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := fun hb => hnl (Or.inl hb)
    have e1 : (withNext P.par b.1).loc.psiSh.map OnBytes.Model.Reading.gl.val =
        List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
      show b.1.loc.psiSh.map _ = _
      rw [hpsi]
      exact hsh
    have eg : (gamma P.par.S (withNext P.par b.1).loc).map OnBytes.Model.Reading.gl.val =
        List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
          (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
      unfold gamma
      rw [List.map_drop, e1]
      exact drop_ofFn P.par.S.kLo P.par.S.fold.index.v _
    have et : ((withNext P.par b.1).loc.psiSh.take P.par.S.kLo).map
        OnBytes.Model.Reading.gl.val = List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
          (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
      rw [List.map_take, e1]
      exact take_ofFn P.par.S.kLo P.par.S.fold.index.v _
    have eapp : List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
          (gVec P.par.S.kCol _ (valsOf (toRD d) c))) ++
        List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
          (gVec P.par.S.kCol _ (valsOf (toRD d) c))) =
        List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
      rw [← take_ofFn, ← drop_ofFn]
      exact List.take_append_drop _ _
    rw [hy, tabOf_imp] at hnear
    obtain ⟨hdec, hU⟩ := hgood a (withNext P.par b.1) (rg w) _ ha hnb eg hkeyE hco hnear hrec
    refine ⟨hpa, hdec, ?_⟩
    by_contra hn
    refine hnl (Or.inr ⟨w, hpa, hn, ?_⟩)
    unfold DotUAt at hdot
    rw [et, e1, ← eapp] at hdot
    have hfin := dotTrue_of P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v (Tab a) _ _ g
      (uOf (withNext P.par b.1).loc (rg w)) (wv w) (by simp) hU hdot
    rw [eapp] at hfin
    exact hfin

end Desc.K14.Law
