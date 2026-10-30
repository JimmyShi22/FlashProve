-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealFill.lean: WHAT THE SEAL's TIE ASKS OF THE TABLE's LETTERS
(FillSeal, Johnson/Desc/K13/Law/AtTableSeal.lean) IS HAD AT meaningSig
(Johnson/Desc/Sound/BordersFill.lean: the table's files' filling BY SIGNATURE), FROM TWO
COMPARISONS OF THE PLAN's NUMBERS WITH THE PIECE's BASE, TWO FACTS ON THE TABLE AND ONE CONDITION ON
THE LETTER pileOne. Statements with their proofs: a joining of K13's files and the table's.
(Namespace VerifiableInference.Desc.Sound: the table's types' own.)
AT meaningSig. At mg1Joint (Johnson/Desc/Sound/JointFilling.lean), the filling that the table's
files mean, and at the two written lists: Johnson/Desc/K13/Law/AtTableSealJoint.lean.

OBJECT. meaningSig's filled letters pin · noColl · shown · pinW · decodes.
USER. seal_tied | firstEnd_tied_seat | firstEnd_tied_lift's premise hF.
LETTERS. cs G arr smp ms decT Mg (the table's files') · N · B.
FIELD. first_chain_knows_means (Johnson/Goal/Skeleton/ProofFile.lean), through chainOfPromises.

Main names:
  fillSeal_sig   **FillSeal at meaningSig**: by decodesOf_cell · shownJT_col ·
    noCollJT_col · pinJT_col · pinWOf_cell (Johnson/Desc/Sound/ReadsTreeAt.lean): CALLED. From: hO
    (nothing is open in front but "no mark", three pins and the one claim) · hI | hV (the index
    masks' and W's tenants sit in trees below B) · hOp (the riders are the three pins and the one
    claim) · hP (the one claim's letter goes back over the strings: at a filling that drops the
    strings, as mg1Joint's does: for nothing).
  seal_extQ   EachExtQ's clause at the seal, of any piece with the identity for its extractor: by
    extQ_id (Johnson/Desc/Sound/BordersFill.lean), from RowSeal.lays.
  firstEnd_tied_sig   **the seal's five ties at that filling**, lifted.
What is not claimed. hT, hO and hR have members at both written lists
(Johnson/Desc/K13/Law/AtTableSealRow.lean): not called here: in AtTableSealJoint.lean. hI | hV are
shown of no plan's numbers; TWO NUMBERINGS OF TREES ARE TIED BY NOTHING: N.index.1 and N.w.1 count
in the BOOK's numbering (N.treesAt), the piece's base in the FILE's: "base = N.treesAt ps[k]?" is
asked nowhere; at a base laid too high hI | hV cost nothing. All that AtTableSeal.lean does not
claim. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSeal
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice OnBytes.Flat Iop Run
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.K13.Law (SameBelow RowSeal FillSeal pieceSeal firstEnd_tied_lift
  openAt sampled_of_open)

/-- **FillSeal at the table's files' filling by signature.** -/
theorem fillSeal_sig (cs : OnBytes.Codes) {Xi Pp Cells Tok : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (N : Numbers) (B : ℕ) (O : List Item)
    (Op : Item → Prop)
    (hO : ∀ i ∈ O, i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hI : N.index.1 < B) (hV : N.w.1 < B)
    (hOp : ∀ i, Op i → i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hP : ∀ x y y' w, SameBelow B y y' → Mg.pileOne x y' w → Mg.pileOne x y w) :
    FillSeal N (meaningSig cs G arr smp ms decT Mg) B O Op :=
  have hS : ∀ t ∈ First.sampledIn N O, t.1 < B := fun t ht => by
    rcases sampled_of_open N O hO t ht with rfl | rfl
    · exact hI
    · exact hV
  { decodes := fun x y y' h hd => decodesOf_cell decT x y y' (fun z => by rw [h.1]) hd
    shown := fun t ht y y' h hs => shownJT_col cs G ms t.1 t.2 y y' (h.2 t.1 (hS t ht)) hs
    noColl := fun t ht x y y' h hn =>
      noCollJT_col cs G smp ms t.1 t.2 x y y' (h.2 t.1 (hS t ht)) hn
    back := fun i hi x y y' w h hw => by
      rcases hOp i hi with rfl | rfl | rfl | rfl
      · exact pinWOf_cell decT x y' y w (fun z => by rw [h.1]) hw
      · exact pinJT_col cs G arr smp ms N.index.1 N.index.2 x y' y w
          (fun z => (h.2 _ hI z).symm) hw
      · exact pinJT_col cs G arr smp ms N.w.1 N.w.2 x y' y w (fun z => (h.2 _ hV z).symm) hw
      · exact hP x y y' w h hw }

/-- **THE EXTRACTOR's OTHER DEBT**: EachExtQ's clause at block k, of any piece whose extractor is
the identity: the table's own extractor lays nothing at the seal's row (extQ_id). -/
theorem seal_extQ (cs : OnBytes.Codes) {A Xi Pp Cl Cells Tok : Type} {C : PQ.CK} {Fr : Frame}
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
    (tokOf : Pp × S → Tok) (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (p : Place) (hT : RowSeal N M links ps k p)
    (q : Piece C Fr A Cl (Wit Cells Tok MsgT)) (hext : ∀ a τ w, q.ext a τ w = w) :
    ∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w := by
  intro a τ b w _
  rw [hext]
  unfold extQAt
  rw [hT.place]
  exact (extQ_id cs G arr smp ms decT c₀ tokOf N links p hT.lays _ _ _ w).symm

/-- **THE SEAL's FIVE TIES AT THE TABLE's FILES' FILLING BY SIGNATURE**, lifted. -/
theorem firstEnd_tied_sig {A Pp Cl Cells Tok Xi : Type} {C : PQ.CK} (F : Frame) (piece : ℕ)
    (front : List (Block S Cl)) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (err : Err (uLT C ds)) (c : Block S Cl) (hc : c.UnderR (First.firstEnd piece front))
    (gt : A → S) (st : A → S → A) (h1 : ∀ t s, gt (st t s) = s)
    (h2 : ∀ t s s', st (st t s) s' = st t s') (pub : A → Pp)
    (hpub : ∀ t s, pub (st t s) = pub t) (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (p : Place) (hT : RowSeal N Mg.more links ps k p)
    (hR : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
      ¬ insQ links ps k i → i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hO : ∀ i ∈ openAt links ps k,
      i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hI : N.index.1 < base) (hV : N.w.1 < base)
    (hP : ∀ x y y' w, SameBelow base y y' → Mg.pileOne x y' w → Mg.pileOne x y w) :
    TiedAt N (meaningSig cs G arr smp ms decT Mg) links ps (fun a : A => (pub a, gt a)) k
      (((pieceSeal (W := Wit Cells Tok MsgT) F piece front base ds back err).seat c).lift gt st) :=
  firstEnd_tied_lift F piece front base ds back err c hc gt st h1 h2 pub hpub N _ links ps k p hT
    (fillSeal_sig cs G arr smp ms decT Mg N base _ _ hO hI hV hR hP)

end VerifiableInference.Desc.Sound
