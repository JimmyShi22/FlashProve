-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawYes.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW IN THE PLAIN FORM
FAILS AT THE TEXT THAT SAYS YES TO ALL.

A law on a verifier's text that a text with the decision "yes to all" also meets says nothing of the
text. `hear_keepsW` (Johnson/Desc/First/K8/LawKeeps.lean) is tried here against that text, at the
closed member of the letters of Johnson/Desc/First/K8/LawPieceToy.lean (the library's own toy
caller: one matrix with one cell and one column, one read, one combination).
  `pieceOf b p base e`: any block at the kind's stretch. `step_of_rounds`, `stretch_free`: a block
    with the kind's round reads no column; the stretch's tests in front of the run pass at every
    written transcript, and no column is shown.
  `pieceOf_out`: GENERAL: at the kind's stretch a block with the kind's round puts out just what its
    decision hands on, at every written transcript: the converse of `piece_out`.
  `toyYes`: the kind's text at the toy's seat with a decision that says yes to all and hands the
    record on as it came.
  `toyBad`, `toyWorld`: a statement in front with the condition: the committed message has the
    symbol 1 and the read 2, so there is no cell; and the record ALREADY HOLDS the list of the
    matrix 0, at which every tie and every read holds whatever is committed (`toyZero_out`).
  `toyYes_all_lost`: at that statement, whatever the prover sends, EVERY written verifier message is
    lost: the text puts out, what stands behind holds at the world, what stands in front does not.
  `toyYes_not_keeps`: so that text has the plain form between these boundaries at NO error below the
    round's whole number of challenges. The kind's own text has it at `toyErr` (`toy_piece_good`).
WHY THE KIND'S OWN TEXT ESCAPES: it refuses a record in which a matrix is already drawn, and lays
the list of the matrix that the round's own verifier message gives: so the matrix behind is not the
prover's to choose.
THE OTHER SILLY TEXT, with the decision "no to all", never puts out, and the plain form says nothing
on acceptance: such a text meets it for nothing (not typed here). What shuts it out is the law's
other half, `hear_law_view`, an "if and only if" (`sillyNo_law`, Johnson/Desc/First/K8/Law.lean).
Definitions, statements and proofs. Limits: a toy. NOT SHOWN: that `toyErr` is below the round's
number of challenges: so the two theorems together do not yet part the two texts by a number. A
prover's message m of the round is an argument.

-/
import Johnson.Desc.First.K8.LawKeeps
import Johnson.Desc.First.K8.LawPieceToy
import Johnson.Desc.First.K8.LawOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj
  KObj.TailRow VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

section
variable {S Cl W : Type} {F : Frame}

/-- Any block at the kind's stretch. -/
def pieceOf (b : Block S Cl) (p : Par) (base e : ℕ) : Piece (Run.ckP .two) F S Cl W where
  b := b
  base := base
  ds := [rdt p]
  ext := fun _ _ w => w
  err := ((e, ()) : ℕ × Unit)

/-- A block with the kind's round reads no column: as a step it is its decision. -/
theorem step_of_rounds (b : Block S Cl) (p : Par) (hb : b.rounds = [round p]) (ft : Nat) (st : S)
    (r : Fmt.RoundView) (cols : List Col) (hfit : roundsFit [round p] [r] = true) :
    b.step ft st [r] cols = (b.decide st [noDigest r] []).map fun s' => (s', 0) := by
  have hg : groupsOf ft [round p] ([r].map (·.drawn)) = [] := by
    simp [groupsOf, round]
  unfold Block.step
  rw [hb, hfit, hg]
  simp only [need, List.flatMap_nil, List.length_nil, List.take_zero, List.map_nil, List.map_cons,
      regroup]
  cases b.decide st [noDigest r] [] <;> rfl

/-- The stretch's tests in front of the run pass at every written transcript, and no column is
shown. -/
theorem stretch_free (b : Block S Cl) (p : Par) (base e : ℕ) (y : F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) :
    sTests (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage y
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = true ∧
      (sView (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage y
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))).opened = [] := by
  have hw : ∀ X : List Fmt.Drawn, wantsOf F.a (pieceOf (W := W) (F := F) b p base e).stage.depth
      [rdt p] X = [] := by
    intro X
    cases X <;> simp [wantsOf, rdt]
  have hfull : ∀ X : List Fmt.Drawn, fullOf [rdt p] X = true := by
    intro X
    cases X <;> simp [fullOf, rdt]
  have hpass : okT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) :=
    (okT_one (rdt p) m c).2 (pass_rng (p := p) c)
  have hw1 : ∀ X : List Fmt.Drawn, wantsOf (pieceOf (W := W) (F := F) b p base e).stage.a
      (pieceOf (W := W) (F := F) b p base e).stage.depth
      (pieceOf (W := W) (F := F) b p base e).stage.ds X = [] := hw
  have hfull1 : ∀ X : List Fmt.Drawn,
      fullOf (pieceOf (W := W) (F := F) b p base e).stage.ds X = true := hfull
  constructor
  · unfold sTests sWants
    rw [hw1, hfull1]
    simp only [sCarries, List.all_nil, Bool.and_true]
    exact hpass
  · have key : ∀ ρ, sWants (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage ρ = [] :=
      fun _ => hw1 _
    simp only [sView, key, List.filterMap_nil]

/-- **At the kind's stretch a block with the kind's round puts out just what its decision hands
on**: at every written transcript. -/
theorem pieceOf_out {s : Size} (b : Block S Cl) (p : Par) (hb : b.rounds = [round p])
    (hf : Fits p s)
    (base e : ℕ) (a : S × F.E.Str) (m : (roundT (Run.ckP .two) (rdt p)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) (st' : S)
    (hd : b.decide a.1 [noDigest (rvOne (rdt p) m c)] [] = .ok st') :
    (pieceOf (W := W) (F := F) b p base e).ior.red.out a
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) =
      some (st', (pieceOf (W := W) (F := F) b p base e).ior.imp a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) := by
  obtain ⟨ht, ho⟩ := stretch_free (W := W) b p base e a.2 m c
  obtain ⟨h1, h2, h3, h4⟩ := view_round hf m c
  have hfit := fit_of hf c _ h1 h2 h3 h4
  have hstep := step_of_rounds b p hb F.ft a.1 (rvOne (rdt p) m c) [] hfit
  rw [hd] at hstep
  have hchain : chainAt b.name F.ft [b] a.1 ⟨[rvOne (rdt p) m c], []⟩ = .ok st' := by
    have hl : b.rounds.length = 1 := by rw [hb]; rfl
    simp [chainAt, foldBlocks, hl, hstep, Except.map]
  show ((if sTests (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) then
      (pieceOf (W := W) (F := F) b p base e).run a.1
        (sView (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage a.2
          ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) else none).map fun xo =>
      (xo, (pieceOf (W := W) (F := F) b p base e).ior.imp a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])))) = _
  rw [if_pos ht]
  have hrun : (pieceOf (W := W) (F := F) b p base e).run a.1
      (sView (Run.ckP .two) (pieceOf (W := W) (F := F) b p base e).stage a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) = some st' := by
    show (chainAt b.name F.ft [b] a.1 ⟨[rvOne (rdt p) m c] ++ [], (sView (Run.ckP .two)
      (pieceOf (W := W) (F := F) b p base e).stage a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))).opened⟩).toOption = some st'
    rw [ho, List.append_nil, hchain]
    rfl
  rw [hrun]
  rfl

end

/-! ## The text with a decision that says yes to all, at the toy -/

/-- The kind's text at the toy's seat, with a decision that says yes to all and hands the record on.
-/
def toyYes : Block ToyS Unit := { approximateRangeProofDrawKind toySeatP toyPar with decide := fun s _ _ => .ok s }

/-- That text at the kind's stretch. -/
abbrev toyYesPiece (base e : ℕ) :
    Piece (Run.ckP .two) toyFrame ToyS Unit (KTailRngOn.src toyOn).W :=
  pieceOf toyYes toyPar base e

/-- The typed matrix whose one entry has the value 0. -/
def toyZero : Dr toyOn.c.s := Cb.Pv.Tail.Toy.dr (false, false)

/-- A statement in front: "true"; the committed message has the symbol 1 and the read 2: there is no
cell; and THE RECORD ALREADY HOLDS A MATRIX'S LIST: that of the matrix 0. -/
def toyBad (y : toyFrame.E.Str) : ToyS × toyFrame.E.Str :=
  ((((true, Cb.Tw.idSmp Cb.Gl.E Unit fun _ => Fin 2),
    ((), Cb.Tw.idStr Cb.Gl.E Unit (fun _ => Fin 2) (toyMsg 1 2))), listOf toyZero), y)

/-- The world: that message; the digits 0 and 1, whose combination is 0. -/
def toyWorld : (KTailRngOn.src toyOn).W :=
  (Cb.Tw.idWit Cb.Gl.E Unit (fun _ => Fin 2) (toyMsg 1 2), ⟨fun _ _ _ => 0, fun _ _ _ => 1⟩)

theorem toyBad_on (base e : ℕ) (y : toyFrame.E.Str) : (toyReads base e).onA (toyBad y) :=
  ⟨Cb.Tw.sigId_cf Cb.Gl.E Unit (fun _ => Fin 2) _, trivial, rfl⟩

theorem toyBad_relA (base e : ℕ) (y : toyFrame.E.Str) :
    ¬ (toyReads base e).relA (toyBad y) toyWorld :=
  toy_relA_fails base e (toyBad y) toyWorld rfl rfl

/-- The combination that the world's digits give is 0. -/
theorem toyComb0 (μ : Fin 1) (u : Fin 1) (i : Fin 1) :
    Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyWorld.2 μ u i = 0 := by
  show (0 : Cb.Gl.E) + ((2 : ℕ) : Cb.Gl.E) * 1 - ((2 : ℕ) : Cb.Gl.E) = 0
  ring

/-- At the matrix 0 every tie and every read holds, whatever is committed. -/
theorem toyZero_out : Cb.Pv.Tail.relOut toyOn.c.letters true toyZero (toyMsg 1 2) toyWorld.2 :=
  ⟨fun _ _ _ => ⟨⟨0, by norm_num, by simp [toyWorld]⟩, ⟨1, by norm_num, by simp [toyWorld]⟩⟩,
    fun μ u i' => by
      show ∑ _c : Fin 1, (((0 : ℤ) : ℤ) : Cb.Gl.E) * (1 : Cb.Gl.E) =
        Alg.pack ((4 : ℕ) : ℤ) (Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyWorld.2 μ u) i'
      rw [toyPack, toyComb0]
      simp,
    fun μ u _ => by
      show ∑ _c : Fin 1, (((0 : ℤ) : ℤ) : Cb.Gl.E) * (2 : Cb.Gl.E) =
        ∑ i : Fin 1, (1 : Cb.Gl.E) * Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyWorld.2 μ u i
      simp [toyComb0]⟩

/-- So what stands behind holds at the record as it came. -/
theorem toyBad_relB (base e : ℕ) (y y' : toyFrame.E.Str) :
    (toyReads base e).relB ((toyBad y).1, y') toyWorld :=
  (toyReads base e).relB_of_one _ _ toyZero rfl
    ⟨Cb.Tw.sigId_decs Cb.Gl.E Unit (fun _ => Fin 2) (toyMsg 1 2), trivial, toyZero_out⟩

/-- **At that statement the text that says yes to all is lost at EVERY written verifier message.**
-/
theorem toyYes_all_lost (base e : ℕ) (y : toyFrame.E.Str)
    (m : (roundT (Run.ckP .two) (rdt toyPar)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt toyPar)).up.Chal) :
    ¬ ∀ b, (toyYesPiece base e).ior.red.out
        (toyBad y) ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt toyPar])) = some b →
      (toyReads base e).onB b ∧
        ∀ w, (toyReads base e).relB b w → (toyReads base e).relA (toyBad y) w := by
  intro h
  have ho := pieceOf_out (W := (KTailRngOn.src toyOn).W) (F := toyFrame) toyYes toyPar rfl toyFitsOn
    base e (toyBad y) m c (toyBad y).1 rfl
  exact toyBad_relA base e y ((h _ ho).2 toyWorld (toyBad_relB base e y _))

/-- **So it has the plain form at no error below the round's whole number of challenges.** -/
theorem toyYes_not_keeps (base e : ℕ) (y : toyFrame.E.Str)
    (m : (roundT (Run.ckP .two) (rdt toyPar)).up.Msg)
    (he : e < Nat.card (roundT (Run.ckP .two) (rdt toyPar)).up.Chal) :
    ¬ (toyYesPiece base e).ior.red.KeepsW
      (toyReads base e).onA (toyReads base e).onB (toyReads base e).relA (toyReads base e).relB
      (toyYesPiece base e).err := by
  intro h
  have hd : cnt (fun c : (roundT (Run.ckP .two) (rdt toyPar)).up.Chal =>
      ¬ ∀ b, (toyYesPiece base e).ior.red.out
          (toyBad y) ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt toyPar])) = some b →
        (toyReads base e).onB b ∧
          ∀ w, (toyReads base e).relB b w → (toyReads base e).relA (toyBad y) w) ≤ e :=
    h (toyBad y) (toyBad_on base e y) m
  have hc : Nat.card (roundT (Run.ckP .two) (rdt toyPar)).up.Chal ≤ cnt (fun c :
      (roundT (Run.ckP .two) (rdt toyPar)).up.Chal =>
      ¬ ∀ b, (toyYesPiece base e).ior.red.out
          (toyBad y) ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt toyPar])) = some b →
        (toyReads base e).onB b ∧
          ∀ w, (toyReads base e).relB b w → (toyReads base e).relA (toyBad y) w) :=
    Nat.card_le_card_of_injective (fun c => ⟨c, toyYes_all_lost base e y m c⟩)
      (fun _ _ hab => congrArg Subtype.val hab)
  exact absurd (le_trans hc hd) (not_le.2 he)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.pieceOf_out
#print axioms VerifiableInference.Desc.First.K8.toyYes_all_lost
#print axioms VerifiableInference.Desc.First.K8.toyYes_not_keeps
