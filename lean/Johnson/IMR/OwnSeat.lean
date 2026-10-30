-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OwnSeat.lean: AT THE PROOF FILE's SEAT: at every record that the first chain's
fold passes through in front of the blocks behind the last link, RecAll AND the invariant OwnInv
hold at the plan's own letters; so, WHERE A LINK IS OPEN IN THE RECORD, THE LOOKUPS' TIE OwnIs HOLDS
AT THAT LINK's OWN NUMBER. Johnson/IMR/SeatKeeps.lean at two relations at once (SeatKeeps.and).

Compiled with the whole library.

  ArrOk A built, seatKeeps_own   SeatKeeps (OwnRel A lay) (ArrOk A) (fun P => P.X.arrayOf = A P.l):
    a field a line.
  arrOf Z l, sentAt Z, arrOk_at   the built links' lists of arrays; the lookups' public record off
    the public part: ⟨Z.first.codes, Z.first.shape, Z.first.layout, Z.p.built.links.map
    (·.arrayOf)⟩.
  blank_built, letters_arr   the head's link's letters are made off the blank letters, whose links
    are the built links but for their routines: so they bear the built link's list of arrays.
  own_startS   the invariant at the first record, where the request passes reqOk.
  BothAt Z t, descPure_both   RecAll Z.first.codes Z.first.shape t ∧ OwnInv (arrOf Z) Z.first.layout
    t, at every fold from the first record over a front part of frontOf c.
  ownIs_lay, ownIs_att, ownIs_head   BothAt Z t and t.here = .lay a | .att a | .head a (opened) give
    OwnIs (sentAt Z) a.L.link t.
  descPure_both_run   THE JOIN TO THE DECISION: from a yes of F.run: by cut, and by place (l, i).

OBJECT: ProofFile.onlineDescription's value at every o; OwnIs.
LETTERS: none free but the files and
the views.

WHAT IS NOT SAID. THAT AT THE PLACE (l, i) A LINK IS OPEN AND ITS NUMBER IS l: OwnIs stands at
a.L.link, the number that the record bears. No soundness.
-/
import Johnson.IMR.K2ShareAt
import Johnson.Goal.Meaning.OwnMakers
import Johnson.Goal.Meaning.K2Share.OwnKept
import Johnson.Goal.Meaning.OwnIsOfRec
import Johnson.Goal.Meaning.OwnOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape ReqLayout)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.First.Look (Sent OwnIs)
open ProofFile (Pub)

/-! ## The seat keeps the invariant -/

variable {A : Nat → Array (Nat × String)} {lay : ReqLayout}

/-- A is the built links' own lists of arrays. -/
def ArrOk (A : Nat → Array (Nat × String)) (built : Array Stages.LinkH) : Prop :=
  ∀ l X, built[l]? = some X → X.arrayOf = A l

theorem seatKeeps_own :
    SeatKeeps (OwnRel A lay) (ArrOk A) (fun P => P.X.arrayOf = A P.l) where
  refl := ownRel_refl
  trans := ownRel_trans
  frames := fun hB h => framesOf_own hB h
  k1First := fun q gp _ => whole_ownC (firstAtS_ctx q gp)
  k1Later := fun _ _ l _ m a _ => whole_ownC (commitAtS_ctx _ l m a)
  reads := fun h => whole_own (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_own (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_own (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_own (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_own (seatedClaims_quiet h)
  k7 := fun W l => whole_own (k7Of_quiet W l)
  k8 := fun p => whole_own (k8Whole_quiet p)
  k11 := fun P => whole_own (headMerge11_quiet P)
  closeOf := closeOf_own
  batch := fun p _ hf => batch_own p hf
  k2 := fun p _ => First.K2.k2_ownRel p
  front := First.K2.headFrontQ_ownRel
  openQ := First.K2.headOpenQ_ownRel
  finFront := First.K2.finishFrontQ_ownRel
  finBehind := First.K2.finishBehindQ_ownRel

/-! ## At the proof file's seat -/

/-- The built links' lists of arrays, by the link's number. -/
def arrOf (Z : Pub) (l : Nat) : Array (Nat × String) :=
  (Z.p.built.links.map (·.arrayOf)).getD l #[]

/-- The lookups' public record, off the description's public part. -/
def sentAt (Z : Pub) : Sent :=
  ⟨Z.first.codes, Z.first.shape, Z.first.layout, Z.p.built.links.map (·.arrayOf)⟩

theorem arrOk_at (Z : Pub) : ArrOk (arrOf Z) Z.p.built.links := fun l X h => by
  unfold arrOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, h]
  rfl

/-- The blank letters' links are the built links, but for their routines. -/
theorem blank_built {mk : ProofFile.LinksBy} {Z : Pub} {G : ProofFile.Ground} (h : ProofFile.blankBy mk Z = some G) :
    ∃ links : Array Stages.LinkH,
      G.built = Z.p.built.links.zipWith (fun b l => { b with run := l.run }) links := by
  have h' : (ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption =
      some G := h
  cases hx : ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    obtain rfl : G' = G := Option.some.inj h'
    unfold ProofFile.lettersBy at hx
    simp only [bind, Except.bind, pure, Except.pure] at hx
    repeat' split at hx
    all_goals first | contradiction | (cases hx; exact ⟨_, rfl⟩)

/-- **The head's link's letters, off the blank letters, bear the built link's list of arrays.** -/
theorem letters_arr {mk : ProofFile.LinksBy} {Z : Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : Nat} {P : First.K2.HeadPar}
    (hP : P1K2.pureLetters G l = some P) : P.X.arrayOf = arrOf Z P.l := by
  obtain ⟨links, e⟩ := blank_built h
  unfold P1K2.pureLetters at hP
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hP
  show X'.arrayOf = arrOf Z l
  rw [e] at hX'
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hX'
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact arrOk_at Z l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

/-- **The first chain's first record**, where the request passes the tests that read no reply. -/
theorem own_startS {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) {p : ProofFile.InstPub}
    (hq : (Z.s₀.withReq (Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) :
    OwnInv A Z.first.layout (ProofFile.startS Z p) := by
  unfold ProofFile.startS
  dsimp only
  rw [if_pos hq]
  have hs := pub_start h
  unfold S.startP at hs
  split at hs
  · have e := Option.some.inj hs
    rw [← e]
    exact ⟨rfl, fun x hx => nomatch hx⟩
  · cases hs

/-- RecAll and the invariant, at the plan's own letters. -/
def BothAt (Z : Pub) (t : S) : Prop :=
  RecAll Z.first.codes Z.first.shape t ∧ OwnInv (arrOf Z) Z.first.layout t

/-- **At every record that a fold from the first record passes through in front of the blocks behind
the last link.** -/
theorem descPure_both {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol ly KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol ly KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧
      ∀ (x : ProofFile.Inst), ProofFile.okBy o ProofFile.pureRoad.links Z x = true →
        ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : Cols) (r : S × List Fmt.RoundView × Cols),
          foldBlocks ft l₁ (ProofFile.startS Z x.pub) rs cols = .ok r → BothAt Z r.1 := by
  obtain ⟨Z, hZ, -⟩ := ProofFile.Law.descPure_made h
  have H := (seatKeeps_rec (k2Share Z.first.codes Z.first.shape)).and
    (seatKeeps_own (A := arrOf Z) (lay := Z.first.layout))
  obtain ⟨Z', A, B, c, hZ', e, k0, k⟩ := descPure_keepsP H
    (fun Z'' hZ'' => by
      obtain rfl : Z = Z'' := Except.ok.inj (hZ.symm.trans hZ'')
      exact ⟨trivial, arrOk_at Z⟩)
    (fun Z'' hZ'' G hG l P hP => by
      obtain rfl : Z = Z'' := Except.ok.inj (hZ.symm.trans hZ'')
      exact ⟨trivial, letters_arr hG hP⟩) h
  obtain rfl : Z = Z' := Except.ok.inj (hZ.symm.trans hZ')
  refine ⟨Z, A, B, c, hZ, e, k0, fun x hx l₁ l₂ hl ft rs cols r hf => ?_⟩
  have q := Keeps.foldBlocks_keeps _ H.refl H.trans ft l₁
    (fun b hb => k b (hl ▸ List.mem_append_left _ hb)) _ rs cols r hf
  exact ⟨q.1 (recAll_startS hZ (okBy_reqOk hx)), q.2 (own_startS hZ (okBy_reqOk hx))⟩

/-! ## The lookups' tie -/

/-- **Where a layers' link is open in the record, the record's own five are the public part's, at
that link's own number.** -/
theorem ownIs_lay {Z : Pub} {t : S} (K : BothAt Z t) {a : LayOwn} (h : t.here = .lay a) :
    OwnIs (sentAt Z) a.L.link t :=
  ownIs_of_rec (D := sentAt Z) K.1
    ⟨⟨a.L, by simp [S.link?, h], rfl, K.2.atLay h⟩, K.2.live⟩

/-- **The like at an attention link.** -/
theorem ownIs_att {Z : Pub} {t : S} (K : BothAt Z t) {a : AttOwn} (h : t.here = .att a) :
    OwnIs (sentAt Z) a.L.link t :=
  ownIs_of_rec (D := sentAt Z) K.1
    ⟨⟨a.L, by simp [S.link?, h], rfl, K.2.atAtt h⟩, K.2.live⟩

/-- **The like at the head's link, behind its opening.** -/
theorem ownIs_head {Z : Pub} {t : S} (K : BothAt Z t) {a : HeadOwn} (h : t.here = .head a)
    (ho : a.opened = true) : OwnIs (sentAt Z) a.L.link t :=
  ownIs_of_rec (D := sentAt Z) K.1
    ⟨⟨a.L, by simp [S.link?, h, ho], rfl, K.2.atHead h ho⟩, K.2.live⟩

/-- **The three in one, off ctxOf**: where the record's context counts as open and bears the number
l, the tie holds at l. -/
theorem ownIs_of_ctx {Z : Pub} {t : S} (K : BothAt Z t) {m l : Nat} {r : ReqRows}
    {ar : Array (Nat × String)} (h : (ctxOf t).2 = some (m, r, l, ar)) (hm : m ≠ 1) :
    OwnIs (sentAt Z) l t := by
  obtain ⟨L, h1, h2, h3, -⟩ := link_of_ctx h hm
  refine ownIs_of_rec (D := sentAt Z) K.1 ⟨⟨L, h1, h2, ?_⟩, K.2.live⟩
  rw [h3]
  exact (K.2.2 _ h).2 hm

/-- **A YES OF THE FILE's DECISION**: at every cut of frontOf c, and by place at the record in front
of block number i in front of the batching of link number l: RecAll and the invariant. -/
theorem descPure_both_run {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol ly KL = .ok F) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol ly KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      (∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
          foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
            .ok (t, rs, cols) ∧
          foldBlocks 0 (l₂ ++ backOf c) t rs cols = .ok (e, [], []) ∧ BothAt Z t) ∧
      ∀ (l i : Nat) (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), c.links[l]? = some Lk →
        Lk.hear[i]? = some b →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
          foldBlocks 0 (c.blocksInOrder.take (IM.flatIx c l i)) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened = .ok (t, rs, cols) ∧
          foldBlocks 0 (b :: c.blocksInOrder.drop (IM.flatIx c l i + 1)) t rs cols = .ok (e, [], []) ∧
          BothAt Z t := by
  obtain ⟨Z, A, B, c, hZ, rfl, k0, k⟩ := descPure_both h
  have hflat := flat_eq k0
  obtain ⟨e₁, -, -, -, ho, -, -, -, j₁, -⟩ := (FileDescription.run_ok _ x v₁ v₂ v₃).1 hr
  have hok : ProofFile.okBy o ProofFile.pureRoad.links Z x = true := by
    have ho' : (ProofFile.okBy o ProofFile.pureRoad.links Z x && A.okInst x.pub) = true := ho
    exact (Bool.and_eq_true _ _ ▸ ho').1
  have j : chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ := j₁
  have f := Keeps.chainAt_fold _ _ _ _ _ _ j
  have cut : ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
      ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) ∧
        foldBlocks 0 (l₂ ++ backOf c) t rs cols = .ok (e, [], []) ∧ BothAt Z t := by
    intro l₁ l₂ hl
    have f' := f
    rw [hflat, hl, List.append_assoc] at f'
    obtain ⟨t, rs, cols, f1, f2⟩ := Keeps.foldBlocks_split 0 _ _ _ _ _ _ f'
    exact ⟨t, e₁, rs, cols, f1, f2, k x hok l₁ l₂ hl 0 _ _ _ f1⟩
  refine ⟨Z, A, B, c, hZ, rfl, hflat, cut, fun l i Lk b h1 h2 => ?_⟩
  have hn := flatIx_le k0 h1 h2
  have e1 : c.blocksInOrder.take (IM.flatIx c l i) = (frontOf c).take (IM.flatIx c l i) := by
    rw [hflat, List.take_append_of_le_length hn]
  have e2 : (frontOf c).drop (IM.flatIx c l i) ++ backOf c =
      b :: c.blocksInOrder.drop (IM.flatIx c l i + 1) := by
    obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 (IM.hear_at_flat h1 h2)
    rw [← e, ← List.drop_eq_getElem_cons hlt]
    conv_rhs => rw [hflat]
    rw [List.drop_append_of_le_length hn]
  obtain ⟨t, e, rs, cols, f1, f2, R⟩ := cut _ _ (List.take_append_drop (IM.flatIx c l i) _).symm
  exact ⟨t, e, rs, cols, e1 ▸ f1, e2 ▸ f2, R⟩

#print axioms seatKeeps_own
#print axioms own_startS
#print axioms descPure_both
#print axioms ownIs_lay
#print axioms ownIs_att
#print axioms ownIs_head
#print axioms ownIs_of_ctx
#print axioms letters_arr
#print axioms descPure_both_run

end Meaning.K2
