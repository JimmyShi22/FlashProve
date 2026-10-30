-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TrOnto
import Johnson.Desc.K12.Law.AccKIff
/-
Johnson/Desc/K12/Law/AccKYes.lean: WHERE THE LEMMA's VERIFIER accK HAS A YES: wherever Block.step of proximityTestKind guardedProximityTestParts p says yes on rounds that fit the chain's written rounds' data, with columns read off some tables (one table a written tree), there is a typed transcript at which accK says yes. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  SameOrc c b b'   two families of blocks' transcripts hold the same written oracle in each code switch's first message
  srcFrom_congr · srcFirst_congr · srcK_congr   the written columns hang on the transcripts through these oracles alone
  orcs_split · sameOrc_of_orcs   transcripts of the list of rounds with one family of oracles give SameOrc
  orc1 · orc1_of_orcs   the chain's first message's round and oracle
  accK_yes      for any W that hangs on the oracles alone: τ₀ (it carries the tables: nothing else of it is read) · rs' with Forall₂ RoundIs c.rds rs' · a yes of Block.step at the rounds r0 :: rs' and the columns read off τ₀'s oracles and W ⇒ ∃ τ THAT SHOWS JUST THE ROUNDS rs' (the sealed digests apart) AND HOLDS τ₀'s oracles, accK p F t0 r0 c ts W τ = true. (A carrier τ₀ for any tables: Johnson/Desc/K12/Law/TrOnto.lean's tr_with.)
  accK_yes_wAt  the same at the lemma's own W := wAt c W0 ft fM, for fM that reads the first message's oracle alone (a constant; or the message's own oracle)
WHAT IT IS WORTH, IN OUR FIRST READER's WORDS, TO THE LETTER: «accK, the verifier in the lemma, says yes at some typed transcript wherever three premises are met; that they are met at a real proof is not shown; that any prover is not doomed is not shown (that is completeness's).» WHAT FALLS: «where accK never says yes the lemma is empty». WHAT STANDS: k12_lemma_fwd's premise «¬ Doomed …» wants, at some message of each round in turn, more than the round's count of challenge values behind which the rest is not doomed: a whole tree of accepting transcripts: an honest prover's work, not one τ: IT IS STILL NOT SHOWN TO HAVE A MEMBER. WHEN THIS FILE WAS FIRST FROZEN NO THEOREM AND NO RUN HAD MET THE PREMISES hR AND hstep TOGETHER (every yes of Block.step that has run took a stored proof's own columns, not colsOf … of tables). SINCE: Johnson/Desc/K12/Law/AccKConst.lean AND Johnson/Desc/K12/Law/AccKOwn.lean DERIVE BOTH FROM A YES OF Block.step AT ANY VIEW, TWO NUMBERS OF THE PLACE AND TESTS WITH CODE: SO THE QUOTED SENTENCE's MIDDLE CLAUSE NOW HANGS ON RUNS OF THESE TESTS ALONE. THE THREE, at the real view: (1) the step's yes (has run) · (2) RoundIs of each round behind "BAT": Block.step's own roundsFit gives all of it BUT: that the drawn elements are canonical (three words below the field's size) · logN ≤ 64 · that the elements stand beside Fmt.dsElems in number (drawNZ ≤ drawE: nzOk's) · that the written round's kind is the name's · (3) that the view's columns ARE columns of tables: one tree, one position ⇒ one column, of the tree's width, at a position below the tree's size: SINCE SHOWN, FOR A CONSTANT fM, FROM Block.step's OWN SECOND TEST AND THE PLAN's BOOLEANS: Johnson/Desc/K12/Law/TabsView.lean's tables_of_view; the closed form: Johnson/Desc/K12/Law/AccKHas.lean.
WHAT IT DOES NOT SAY: that the blocks of the transcript are a hash function's answers (the oracle model) · anything of a search: the tests of work pass at τ because its bits of work are laid as zeros · anything on a view from bytes · completeness.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Onto (Orcs orcsOf RoundIs tr_onto step_congr groupsOf_noDigest)

/-- The same written oracle in each code switch's first message. -/
def SameOrc : {s : Sg} → (c : Chain s) → c.Bl → c.Bl → Prop
  | _, .last _ _ _ _ _ _ _ => fun _ _ => True
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun b b' =>
    b.2.1.1.1 = b'.2.1.1.1 ∧ SameOrc next b.2.2 b'.2.2

theorem srcFrom_congr : ∀ {s : Sg} (c : Chain s) (d : PQ.RD) (o : (wRound d).Orc) (b b' : c.Bl),
    SameOrc c b b' → srcFrom c d o b = srcFrom c d o b'
  | _, .last _ _ _ _ _ _ _, _, _, _, _, _ => rfl
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next, d, o, b, b', h => by
    funext l i x
    show (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then colW d o x
      else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
        (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x) =
      (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then colW d o x
      else srcFrom next dS b'.2.1.1.1 b'.2.2 (l.drop (s.h + s.g + 3))
        (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x)
    rw [h.1, srcFrom_congr next dS b'.2.1.1.1 b.2.2 b'.2.2 h.2]

theorem srcFirst_congr : ∀ {s : Sg} (c : Chain s) (b b' : c.Bl), SameOrc c b b' →
    srcFirst c b = srcFirst c b'
  | _, .last _ _ _ _ _ _ _, _, _, _ => rfl
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next, b, b', h => by
    funext l ts gT i x
    show (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
        gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) x
      else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
        (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x) =
      (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
        gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) x
      else srcFrom next dS b'.2.1.1.1 b'.2.2 (l.drop (s.h + s.g + 3))
        (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x)
    rw [h.1, srcFrom_congr next dS b'.2.1.1.1 b.2.2 b'.2.2 h.2]

theorem srcK_congr (p : P12) {s : Sg} (c : Chain s) (b b' : c.Bl) (h : SameOrc c b b') :
    srcK p c b = srcK p c b' := by
  funext ts gT i
  unfold srcK
  rw [srcFirst_congr c b b' h]

theorem orcs_split : ∀ (ds₁ ds₂ : List PQ.RD) (τ τ' : Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂))),
    orcsOf (ds₁ ++ ds₂) τ = orcsOf (ds₁ ++ ds₂) τ' →
    orcsOf ds₁ (splitT ds₁ ds₂ τ).1 = orcsOf ds₁ (splitT ds₁ ds₂ τ').1 ∧
      orcsOf ds₂ (splitT ds₁ ds₂ τ).2 = orcsOf ds₂ (splitT ds₁ ds₂ τ').2
  | [], _, _, _, h => ⟨rfl, h⟩
  | _ :: ds₁, ds₂, (m, _, τ), (m', _, τ'), h => by
    have h1 : m.1 = m'.1 := (Prod.mk.inj h).1
    obtain ⟨a, b⟩ := orcs_split ds₁ ds₂ τ τ' (Prod.mk.inj h).2
    exact ⟨Prod.ext h1 a, b⟩

theorem sameOrc_of_orcs : ∀ {s : Sg} (c : Chain s) (τ τ' : Tr (PQ.uL (ckP .two) c.rds)),
    orcsOf c.rds τ = orcsOf c.rds τ' → SameOrc c (blOf c τ) (blOf c τ')
  | _, .last _ _ _ _ _ _ _, _, _, _ => trivial
  | s, .step _ _ _ _ _ dE dT dS dC _ _ _ _ _ next, τ, τ', h => by
    obtain ⟨_, h2⟩ := orcs_split (foldRds s dE dT) ([dS, dC] ++ next.rds) τ τ' h
    obtain ⟨h3, h4⟩ := orcs_split [dS, dC] next.rds _ _ h2
    exact ⟨(Prod.mk.inj h3).1, sameOrc_of_orcs next _ _ h4⟩

/-- The chain's first message's round and written oracle. -/
def orc1 : {s : Sg} → (c : Chain s) → H2K.Pub.Msg1 c → WO
  | _, .last _ _ dL _ _ _ _ => fun m => ⟨dL, m.1⟩
  | _, .step _ _ _ _ _ dE _ _ _ _ _ _ _ _ _ => fun m => ⟨dE, m.1⟩

theorem orc_head (d : PQ.RD) (ds : List PQ.RD) (τ τ' : Tr (PQ.uL (ckP .two) (d :: ds)))
    (h : orcsOf (d :: ds) τ = orcsOf (d :: ds) τ') : τ.1.1 = τ'.1.1 := by
  obtain ⟨m, _, _⟩ := τ
  obtain ⟨m', _, _⟩ := τ'
  exact (Prod.mk.inj h).1

theorem orc1_of_orcs : ∀ {s : Sg} (c : Chain s) (τ τ' : Tr (PQ.uL (ckP .two) c.rds)),
    orcsOf c.rds τ = orcsOf c.rds τ' →
    orc1 c (H2K.Pub.msg1 c (blOf c τ)) = orc1 c (H2K.Pub.msg1 c (blOf c τ'))
  | _, .last _ _ dL dB _ _ _, τ, τ', h =>
    congrArg (fun o => (⟨dL, o⟩ : WO)) (orc_head dL [dB] τ τ' h)
  | s, .step _ _ _ _ _ dE dT dS dC _ _ _ _ _ next, τ, τ', h =>
    congrArg (fun o => (⟨dE, o⟩ : WO))
      (orc_head dE (List.replicate (s.h + s.g) dT ++ ([dS, dC] ++ next.rds)) τ τ' h)


theorem accK_yes (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s) (ts : List ℕ)
    (W : c.Bl → ℕ → WO)
    (hW : ∀ τ τ' : Tr (PQ.uL (ckP .two) c.rds), orcsOf c.rds τ = orcsOf c.rds τ' →
      W (blOf c τ) = W (blOf c τ'))
    (τ₀ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (hR : List.Forall₂ RoundIs c.rds rs') (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs')
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
        (srcK p c (blOf c τ₀) ts fun z x => colW (W (blOf c τ₀) z).1 (W (blOf c τ₀) z).2 x)) =
      .ok (tE, n)) :
    ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
      orcsOf c.rds τ = orcsOf c.rds τ₀ ∧ accK p F t0 r0 c ts W τ = true := by
  obtain ⟨τ, h1, h2, h3⟩ := tr_onto c.rds rs' hR (orcsOf c.rds τ₀)
  refine ⟨τ, h1, h3, ?_⟩
  have hrs : (r0 :: PQ.rvSL (ckP .two) c.rds τ).map noDigest = (r0 :: rs').map noDigest := by
    rw [List.map_cons, List.map_cons, h1]
  have hg : groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
      ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)) =
      groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)) := by
    rw [← groupsOf_noDigest, hrs, groupsOf_noDigest]
  unfold accK
  rw [h2, hg, srcK_congr p c _ _ (sameOrc_of_orcs c τ τ₀ h3), hW τ τ₀ h3,
    step_congr F _ t0 _ _ _ hrs, hstep]
  rfl

/-- At the lemma's own W. -/
theorem accK_yes_wAt (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W0 : ℕ → WO) (ft : ℕ) (fM : H2K.Pub.Msg1 c → WO)
    (hfM : ∀ m m', orc1 c m = orc1 c m' → fM m = fM m')
    (τ₀ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (hR : List.Forall₂ RoundIs c.rds rs') (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs')
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
        (srcK p c (blOf c τ₀) ts fun z x =>
          colW (wAt c W0 ft fM (blOf c τ₀) z).1 (wAt c W0 ft fM (blOf c τ₀) z).2 x)) =
      .ok (tE, n)) :
    ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
      orcsOf c.rds τ = orcsOf c.rds τ₀ ∧ accK p F t0 r0 c ts (wAt c W0 ft fM) τ = true :=
  accK_yes p F t0 r0 c ts (wAt c W0 ft fM)
    (fun τ τ' h => by
      unfold wAt
      rw [hfM _ _ (orc1_of_orcs c τ τ' h)])
    τ₀ rs' hR tE n hstep

end H2K.JointK

#print axioms H2K.JointK.accK_yes
#print axioms H2K.JointK.accK_yes_wAt
