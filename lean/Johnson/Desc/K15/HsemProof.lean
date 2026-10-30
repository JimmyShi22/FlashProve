-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/HsemProof.lean: THE RECORDS' ROAD's END, GENERAL IN THE SIZES AND THE CHAIN.
  yes_in_field_desc   THE LIBRARY's yes_in_field_manyR (OnBytes/Slice/ManyBlkWrittenRec.lean:53)
  WITH dec := (descOf P plan ok).run (first, further) AND ITS PREMISE hdec GONE: whenever the
  library's written
                      link, at the link's description's own decision, accepts a transcript, the
                      chain's yes in the field holds: c.Acc at sumStmR of the typed statement st4R's
                      rows under the powers of the
                      element that the batching's round drew, at the library's own words wordIn |
                      wordFr of col1.
  BatOk               a PROVED theorem of another file (Johnson/Desc/K12/Law/BatOk.lean: bat_ok) as a proposition:
  A PREMISE here, so that no twin grows
  OpensAt P c         PUBLIC, on the plan: the batching's round opens no tree; OpensAre c at the
  rounds behind it, from the tree number 0 (Johnson/Desc/Link/LinkShown.lean)
  behind_of · keyed_mem   helpers
HOW. accept_view (the library's) → handsOnRun (Johnson/Desc/K15/K15Run.lean: LinkRanR, the tail's
yes, planOk) → tail_yes | test_planOk (Johnson/Desc/K15/HsemOf.lean) → k12_yes_acc
(Johnson/Desc/K12/Law/K12Law.lean: general in the chain) AT
StartK, WHICH IS PAID HERE: stages | pub: PubAt (public) with LinkRanR.codes · rounds: the library's
view_rounds_many · behind the batching: THE CLAIM: the library's head_claimR, with batRan_at |
ran_fresh
(Johnson/Desc/K15/K15Head.lean), gOne_of_els, and hmask out of the library's HeadKeepsR CALLED AS IT
LIES at LinkRanR and BatRan (ctxOf is startCtx by rfl) · ShownLater AND THE FIRST SWITCH's COLUMNS:
shownFrom_of_keys
(Johnson/Desc/Link/LinkShown.lean) from Block.step's own test on the columns, LinkRanR.opened_sub
and the library's shows_many · THE FIRST STAGE's TIE: linkReads (Johnson/Desc/Link/LinkReads.lean)
at the seat that HeadKeepsR's GroupTie hands.
THE PREMISES are yes_in_field_manyR's own public ones (hs0 · HeadTrees · Trees · the length · the
group's facts · LinkSizes · LinkFit · BatDraws · hkeep), KeyHasR ×2, and: samples = 1 · BatOk ·
PubAt · OpensAt · one
equation of widths (hwid). GONE against the library's: hdec · hi0 | hi1 (the run's own test on the
instance pays them) · htest | h2 | hride | hP | hW (PubAt and K12's law stand in their place).
NO RUN OF `verify-on-bytes` STANDS IN A STATEMENT OR A PROOF OF K15's FILES (Johnson/Desc/K15/) ON
THIS ROAD; the library's lemmas that are called take RECORDS (LinkRanR · BatRan) or speak of views
and pure functions.
NOT CLAIMED: soundness by itself: it is hsem, the tie under which the library's link_chain_joh
speaks. That PubAt and OpensAt have a member is shown nowhere yet.
(Where this and lean/THEOREM.md differ, the page holds.)
-/
import Johnson.Desc.K15.HsemOf
import Johnson.Desc.Link.LinkShown
import Johnson.Desc.K12.Law.StepAt
import OnBytes.Slice.ManyBlkWrittenRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The theorem bat_ok (Johnson/Desc/K12/Law/BatOk.lean), as a proposition: what a yes of the
batching's plain text holds. TAKEN AS A PREMISE, so that no twin of it grows here and that file's
imports need not lie beneath this one. -/
def BatOk : Prop :=
  ∀ (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout),
    First.Close.bat S g e r = .ok (row, L, S') →
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ S.layout g = some L ∧ S' = begun S g G ∧
      r.drawn.elems.map E.ofTriple = [x] ∧ Bat.combine S' g ⟨L, runRows S G⟩ x = some row

/-- What is public of the test's declared rounds beside PubAt: which trees they open. -/
structure OpensAt (P : P15) {s : Sg} (c : Chain s) : Prop where
  bat : ksOf (((laidOf (p12Of P)).take 1).map (·.1)) = []
  opens : OpensAre c ((laidS (p12Of P)).map (·.1)) 0

theorem keyed_mem (p : P12) (cut : List Fmt.DeclaredRound) (gs : Gs) (c : Nat × Nat × List UInt64)
    (h : c ∈ keyed p cut gs) : ∃ grp ∈ gs, (c.2.1, c.2.2) ∈ grp := by
  unfold keyed at h
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
  exact ⟨x.2, (List.of_mem_zip hx).2, hy⟩

/-- What StartK asks behind the batching, of three things: the claim; ShownFrom at the whole chain;
the first stage's tie where the first switch's columns are the written oracle's. -/
theorem behind_of {s : Sg} (c : Chain s) (p : P12) (q : GE × (s.cIn.J → GE)) (row : GroupRow)
    (y : s.cIn.Word)
    (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl) (d : PQ.RD) (o : (wRound d).Orc) (l : Laid)
        (gs : Gs)
    (cu : IoppStage) (t : T12) (L : GroupLayout) (ds : List Fmt.DeclaredRound) (fs : Fmt.M1.Stage)
    (rs : List Fmt.M1.Stage) (hstages : stagesOf c = p.nums.stages) (e1 : p.nums.stages = fs :: rs)
    (hcu : stageAt p 0 fs = some cu) (e2 : H2U.roundsOfNums p.nums = some ds) (hq : stmG s row = q)
    (hsh : ShownFrom c d o b l gs)
    (htie : cu.k = s.h + s.g → cu.h = s.h → ∀ poss,
      (∀ x ∈ keyed p (cutS l cu.k) (grpS l cu.k gs), x.2.2 = colW d o x.2.1) →
      ∀ id st book, MaskCase p t (ioppFoldShape cu L) id st book →
        ReadTie p.nums.firstTree s y z (ioppFoldShape cu L) st book id
          (keyed p (cutS l cu.k) (grpS l cu.k gs)) poss) :
    ClaimNow c q row ∧ ShownLater c b l gs ∧ TieNow p cu t L c y z g b l gs := by
  cases c with
  | last s e' dL dB fu fs' εb =>
    exfalso
    have hs : p.nums.stages = [s.st] := hstages.symm
    unfold H2U.roundsOfNums at e2
    rw [hs] at e2
    cases e2
  | step s s' hf n0 e' dE dT dS dC fW fZ fG εf εc next =>
    have hst : s.st = fs := by
      have h1 := hstages.trans e1
      exact (List.cons.inj h1).1
    have hk : cu.k = s.h + s.g := by rw [stageAt_k hcu, ← hst]; rfl
    have hh : cu.h = s.h := by
      unfold stageAt at hcu
      cases hi : p.idx[0]? with
      | none => rw [hi] at hcu; cases hcu
      | some i => rw [hi] at hcu; cases hcu; rw [← hst]; rfl
    refine ⟨hq, hsh.2, fun id st book hm => htie hk hh _ (fun x hx => ?_) id st book hm⟩
    obtain ⟨grp, hg, hm'⟩ := keyed_mem _ _ _ x hx
    rw [hk] at hg
    exact hsh.1 grp hg _ hm'

section
variable (S : Sz) (t₀ lg n : ℕ) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey)
  (es : List Fmt.Entry) (d1 d2 d3 d4 d5 dA : PQ.RD) (c : Chain (S.sg t₀)) (xs : List PQ.XO)

theorem yes_in_field_desc (hbat : BatOk) (hs : P.set.samples = 1) (hpub : PubAt P c P.codes)
    (hopen : OpensAt P c)
    (hs0 : (S.sg t₀).h = 0) (hh : HeadTrees d1 d2 d3 d4 d5 dA)
    (hc : c.Trees) (hl : 1 + c.len ≤ 2 ^ 16) (sh fr : OracleShape)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hwid : 3 * (mem.rows + mem.rows) + fr.maskRows * 3 = Fmt.M2.widthOf S.P.mems 1)
    (hpads : 3 * n ≤ S.P.T.l) (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits P.S.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (P.S.side false 1).index first r.1)
    (hK1 : further.fits P.S.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (P.S.side true 1).index further r.2)
    (hS : LinkSizes S P.S P.codes) (hF : LinkFit S P.S (P.S.side false 1) (P.S.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (P.S.side false 1).columns = P.S.columnsFirst)
    (hn1 : (P.S.side true 1).columns = P.S.columnsFurther)
    (hkeep : ∀ V, HeadKeepsR P.S first further
      (startCtx ⟨es, 1, 0, { codes := P.codes, oracles := #[], groups := #[] },
          { trees := #[], place := #[] }⟩ V) V
      P.codes S.P.Z.l (GroupTie (S.sg t₀) 0 [sh, sh, fr] #[some 0, some f1] #[none, none]))
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl)
    (hacc : (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs
        (fun V => (descOf P plan ok).run (first, further) V)).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true) :
    c.Acc (sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
      (wordIn (S.sg t₀) (col1 S d2 m2.1)) (wordFr (S.sg t₀) (col1 S d2 m2.1)) (g1 m2.1) b := by
  have hv : (descOf P plan ok).run (first, further) (PQ.viewX (ckP .two) _ S.P.T.a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) = true :=
    accept_view _ _ xs _ y _ m0 c0 hacc
  obtain ⟨w0, w1⟩ := shows_many d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hh hc hl
    S.P.T.a xs y
  have hV := view_rounds_many d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b S.P.T.a xs y
  have hop := fun o ho => opened_stored _ S.P.T.a xs y
    (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b) o ho
  generalize PQ.viewX (ckP .two) _ S.P.T.a xs y
    (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b) = V at hv w0 w1 hV hop
  have hV' : V.rounds = rvW d1 m1 c1 :: rvW d2 m2 c2 :: rvW d3 m3 c3 :: rvW d4 m4 c4 ::
      rvW d5 m5 c5 :: rvW dA mA cA :: c.rvs b := hV
  obtain ⟨X, D, d5', rest, cols', d', hRan, hg, hmk, hfold, hi0, hi1, _, hplan⟩ :=
    handsOnRun P plan ok es (first, further) V hs hv
  have hp := hRan.pending
  change V.rounds = _ at hp
  rw [hV'] at hp
  simp only [List.cons.injEq] at hp
  obtain ⟨a1, a2, a3, a4, a5, arest⟩ := hp
  have hleft := hRan.left
  change rest = _ at hleft
  have hrest : rest = rvW dA mA cA :: c.rvs b := hleft.trans arest.symm
  obtain ⟨tE, k, fit, hkk, hcc, hdec⟩ := tail_yes P d5' d' rest cols' hfold
  have hpl := test_planOk P plan ok hplan
  refine k12_yes_acc (p12Of P) hpub.early hpub.answers c _ _ _ _ b (t12Of d5') tE _ _ hpl ?_ hdec
  -- the record in front of the test has the codes
  have hcodes : d5'.st.codes = P.codes := hRan.codes
  -- what Block.step has handed is in the view's list
  have hsub : ∀ o ∈ cols'.take k, o ∈ V.opened := fun o ho =>
    hRan.opened_sub o (List.mem_of_mem_take ho)
  have hRds := H2K.Sw.k12_rounds (Cl := Unit) guardedProximityTestParts (p12Of P) hpl
  refine ⟨hpub.stages, ?_, ?_, ?_⟩
  · intro fs rs cu restI e1 e2 e3
    show c.Pub d5'.st.codes cu restI
    rw [hcodes]
    exact hpub.pub fs rs cu restI e1 e2 e3
  · rw [hrest]
    rfl
  · intro fs rs cu ds e r0 row L S' e1 hcu e2 hr0 hb
    obtain ⟨G0, θ, hG, hL, rfl, hθ, hrow⟩ := hbat _ _ _ _ _ _ _ hb
    have hlaid : laidOf (p12Of P) = ds.zip (p12Of P).oracles := by
      unfold laidOf
      rw [e2]
      rfl
    -- the library's record of the batching, at the carried records
    have hG' : d5'.st.groups[X.group]? = some G0 := by rw [hg]; exact hG
    have hL' : d5'.st.layout X.group = some L := by rw [hg]; exact hL
    have hrow' : Bat.combine (begun d5'.st X.group G0) X.group ⟨L, runRows d5'.st G0⟩ θ = some
        row := by
      rw [hg]; exact hrow
    have hfr := ran_fresh _ _ _ _ _ _ _ hRan G0 hG'
    have hB := batRan_at (es.drop 5) (es.drop 6) d5' rest (rest.drop 1) cols' X.group G0 L θ row hG'
        hfr hL' hrow'
    obtain ⟨_, _, _, _, _, hmask, o, hmo, hTie⟩ := hkeep V X D _ _ G0 L θ row hRan hB
    have hT := hTie _ (sameButNotes_refl _)
    -- the element that the batching's round drew
    have hr0' : r0 = noDigest (rvW dA mA cA) := by
      rw [hrest] at hr0
      exact (List.cons.inj hr0).1.symm
    have hθ' : (rvW dA mA cA).drawn.elems = [θ.triple] := by
      rw [hr0'] at hθ
      obtain ⟨t, ht, rfl⟩ := List.map_eq_singleton_iff.1 hθ
      exact ht
    have hdraw : drawnE dA cA = readE θ := by
      rw [readE_def]
      exact gOne_of_els dA mA cA hθ'
    -- the groups by key
    have hstD : ∀ d ∈ (laidOf (p12Of P)).map (·.1), d.stored = [] := fun d hd => by
      rw [hlaid] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact roundsOfNums_stored _ _ e2 _ (List.of_mem_zip hx).1
    rw [hRds] at fit hcc ⊢
    have hKall := keyedIn_of_step _ _ _ V.opened hstD (by
      simpa using roundsFit_length _ _ fit) hcc hsub
    generalize regroup ((groupsOf 0 ((laidOf (p12Of P)).map (·.1)) (rest.map (·.drawn))).map
        (·.length))
      (cols'.take k) = gs at hKall ⊢
    have hbat0 := hopen.bat
    have hopens := hopen.opens
    unfold laidS at hopens
    rw [hlaid] at hKall hbat0 hopens hstD
    have n0 : nOpen (((ds.zip (p12Of P).oracles).take 1).map (·.1)) = 0 := by
      rw [nOpen_ks _ fun r hr => hstD r (by
        rw [List.map_take] at hr
        exact List.mem_of_mem_take hr), hbat0]
      rfl
    have hK1' : KeyedIn V.opened (ksOf (((ds.zip (p12Of P).oracles).drop 1).map (·.1))) gs := by
      have e : ksOf ((ds.zip (p12Of P).oracles).map (·.1)) =
          ksOf (((ds.zip (p12Of P).oracles).drop 1).map (·.1)) := by
        conv_lhs =>
          rw [← List.take_append_drop 1 (ds.zip (p12Of P).oracles), List.map_append, ksOf_append,
              hbat0,
          List.nil_append]
      rw [← e]
      exact hKall
    rw [n0, List.drop_zero]
    have hsh := shownFrom_of_keys V c d2 m2 0 b ((ds.zip (p12Of P).oracles).drop 1) gs
      (fun r hr => hstD r.1 (List.mem_map_of_mem (List.mem_of_mem_drop hr))) hK1' hopens w0 w1
    refine behind_of c (p12Of P) _ row _ _ _ b d2 m2.1 _ gs cu _ L ds fs rs hpub.stages e1 hcu e2 ?_
        hsh ?_
    · rw [hdraw]
      exact head_claimR S t₀ lg n P.S first further d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5
          c5 _ _ _ X D G0 L θ
        row hS hF hd hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hRan hB a1.symm a2.symm a3.symm a4.symm
            a5.symm hop hmask
    · intro hkk' hhh poss hcols id st book hm
      obtain ⟨ms, hl', hseat⟩ := hT.seat
      obtain ⟨o0, o1, rfl⟩ : ∃ o0 o1, ms = [o0, o1] := List.length_eq_two.1 (by
        have kk := hseat.len
        simp only [List.length_append, List.length_cons, List.length_nil] at kk
        omega)
      rcases hm with ⟨h1, rfl, rfl⟩ | ⟨h1, _⟩
      · have hid : id = o := by
          have h2 : d5'.loc.firstMask = some id := h1
          rw [← hmk, hmo] at h2
          exact (Option.some.inj h2).symm
        subst hid
        exact linkReads _ S (S.sg t₀) hs0 cu L _ _ o0 o1 id 0 d2 m2.1 _ poss sh fr mem hmems hE hm0
            f1 hst hf1 hk hR h3
          hz hfm hfz hwid hkk' hhh hl' ⟨hseat.len, hseat.tree, hseat.shape⟩ hcols
      · exfalso
        have h2 : d5'.loc.firstMask = none := h1
        rw [← hmk, hmo] at h2
        cases h2

end

end Desc.K15

#print axioms Desc.K15.behind_of
#print axioms Desc.K15.yes_in_field_desc
