-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Sound.lean: soundness of the BCS compilation with shared rounds.

The file proves `Spec.bcsSoundBatchG` (Compile/Batch/SpecSoundG.lean). Its hypotheses:
(1) the protocols Test, Link and Batch (`BatchProtocol`, Iop/Batch.lean) are round-by-round sound with round
errors at most εs (`BatchProtocol.Sound`, Iop/Batch.lean);
(2) they are local (`IsLocal`);
(3) Batch's annotation is coherent (`Coherent`);
(4) the wire record (parameters of the compiler, Iop/BatchWire.lean) is well-formed (`W.OKG`; rounds
may have proof-of-work bits; the proof uses nothing of the records of these bits).
Its conclusion: there is an event Bad on traces such that
(a) an algorithm with at most t queries causes Bad with probability at most
t εs + 2 (t + 1)² / 2^lam;
(b) Bad is never undone;
(c) outside Bad, for all proof strings that the compiled verifiers `vT`, `vL`, `vB` accept with
their queries answered from the trace: under Test's root an index is extracted; under Link's second
root the same index as under its first, if there is one; and Batch's request is in the relation
`Rno` (that of `BatchProtocol.Sound`) at the extracted index, if there is one;
(d) also outside Bad, what is extracted under an announced root does not change later.

Words used below. State: the value of a state function on a partial transcript (lean/GLOSSARY.md:
state). Slot, joining round, request tree, trace: lean/GLOSSARY.md. The state event of a protocol:
the answer to a new, rooted query turns the state of its slot's transcript, or of the transcript of
one of its live slots, from 0 to 1 (`Lane.step`, Compile/Batch/Rooted.lean). "Our slot": that of the
accepted proof whose fixed data are C (`Ctx`, `Ours`, Compile/Batch/Chain.lean).

  Part 1  Under the hypotheses of its statement, outside `EM` and `EF` the state stays 0 (`stays0`).
  Part 2  One protocol: outside `EM`, `EF` and its state event, an accepted proof string of a slot
          has its statement, with the extracted external strings (the encodings of the index under
          the roots given to the verifier), in the language, under the further hypotheses of
          `mem_of_accepted`.
  Part 3  The event Bad = `EM` or `EF` (Compile/Batch/Events.lean; E_M, E_F in the comments below)
          or the state event of one of the three protocols (`stepS`).

The instance may enter a Fiat-Shamir chain of Batch in two parts (Compile/Batch/Oracles.lean). The
proof follows the instance that the verifier's chain has taken in, round by round (`instX`,
Compile/Batch/LateX.lean; here `swSt`, `instB`), and uses soundness of Batch in the late form
(`SndBL`, Iop/Batch.lean). The statement and its bound are the same as with the whole instance in
the first query.

Limits: what the head of Compile/Batch/SpecSoundG.lean lists as not said is not said here either.
-/
import Compile.Batch.LateX
import Compile.Batch.SpecSoundG
import Iop.BatchOne

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

/-! ## Part 1. The state stays 0 (under the hypotheses of `stays0`) -/

theorem RecIn.mono {K : ℕ} {t : Tag} {pre pre' : Trace (spec lam K L)} {rc : Rec lam K L t}
    (h : RecIn pre rc) (hs : pre ⊆ pre') :
    RecIn pre' rc := by
  obtain ⟨it, a⟩ := rc
  cases it with
  | lo q => exact hs h
  | jn gq q => exact ⟨⟨h.1.choose, hs h.1.choose_spec⟩, hs h.2⟩
  | sh q => exact hs h

/-- The records of our slot (that of C: `Ctx`, `Ours`, Compile/Batch/Chain.lean) are entries of the
trace. -/
theorem ours_recIn (C : Ctx W) {pre : Tc W} {q : FbIn lam L C.t} {l : List (Rec lam W.K L C.t)}
    {cur : Item lam L C.t} (h : Ours C pre q l cur) : ∀ rc ∈ l, RecIn pre rc := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨slot, sh, c, sd, hr, -, hs, -, hl⟩
  · exact (rooted_good pre _ _ _ h1).2.2.1
  · exact (rooted_good pre _ _ _ h1).1
  · obtain ⟨hsh, iJ, -, hslot⟩ := rooted_good pre _ _ _ hr
    obtain ⟨-, -, h6, h7, -⟩ := hslot c sd hs
    cases sh with
    | nil =>
      rw [slotTr_nil] at hl
      cases hl
      exact h6
    | cons p4 rest =>
      rw [slotTr_cons] at hl
      cases hl
      intro rc hrc
      rcases List.mem_append.1 hrc with h | h
      · exact h6 rc h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨h7, hsh p4 List.mem_cons_self⟩
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
          exact hsh z (List.mem_cons_of_mem _ hz)

theorem occursIn_of_startsWith {K : ℕ} {t : Tag} {pre : Trace (spec lam K L)}
    {cms : List (Dig lam)} {x : Option X} {l : List (Rec lam K L t)}
    (h : StartsWith cms x l) (hin : ∀ rc ∈ l, RecIn pre rc) :
    ∀ c ∈ cms.take 2, (evM lam K L).OccursIn pre c := by
  obtain ⟨q1, a1, rest, salt, rfl, hq⟩ := h
  exact fun c hc => ⟨_, hin _ List.mem_cons_self, evM_occurs_cms a1 hq hc⟩

/-- The first two external roots of our slot (that of C: `Ctx`, `Ours`, Compile/Batch/Chain.lean)
occur before the query or at it. -/
theorem ours_cms (C : Ctx W) {pre : Tc W} {q : FbIn lam L C.t} (a : FsAns lam W.K)
    {l : List (Rec lam W.K L C.t)} {cur : Item lam L C.t} (h : Ours C pre q l cur) :
    ∀ c ∈ C.cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE C.t q a]) c := by
  intro c hc
  rcases h with ⟨h1 | h1, -⟩ | ⟨slot, sh, c', sd, hr, -, hs, -, -⟩
  · obtain ⟨-, -, h3, h4⟩ := rooted_good pre _ _ _ h1
    rcases h4 with ⟨-, salt, hq⟩ | h4
    · exact ⟨_, by simp, evM_occurs_cms a hq hc⟩
    · exact (occursIn_of_startsWith h4 h3 c hc).mono (List.subset_append_left _ _)
  · obtain ⟨h3, h4⟩ := rooted_good pre _ _ _ h1
    exact (occursIn_of_startsWith h4 h3 c hc).mono (List.subset_append_left _ _)
  · obtain ⟨-, iJ, -, hslot⟩ := rooted_good pre _ _ _ hr
    obtain ⟨-, -, h6, -, h8⟩ := hslot c' sd hs
    exact (occursIn_of_startsWith h8 h6 c hc).mono (List.subset_append_left _ _)

/-- Outside E_M and E_F the state stays 0. S is the state function on what is left of the protocol.
front holds the records of the earlier rounds. "Our slot" is that of C (`Ctx`, `Ours`,
Compile/Batch/Chain.lean). Hypotheses:
(1) prjP reads back what embP writes;
(2) a prover message never turns S from 0 to 1 (`ProverLaw`);
(3) the verifier's chain for the remaining rounds runs in the trace (`RunsIn`);
(4) the chain so far had the data of our slot (`PrevOK`);
(5) as long as the round L.late has not come, the chain is in its first local rounds (`LateInv`);
(6) the slot value, if the chain passes the joining round, is under the request root at our slot
number;
(7) no query that has the data of our slot, and whose records hold the instances that the verifier
writes (`LateIs`), turns the state from 0 to 1;
(8) the state is 0 (at `PTr.empty`).
Conclusion: the state of the rest of τ∗ (`trStar`, Compile/Batch/Runs.lean) is 0. -/
theorem stays0 (C : Ctx W) (hM : ¬ EM C.tr) (hF : ¬ EF C.tr) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam W.K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p))
        (prjP : PlainPart (shapeOf L C.t) (annOf L C.t) → Option (PlainPart s A))
        (embP : PlainPart s A → PlainPart (shapeOf L C.t) (annOf L C.t)),
      (∀ z, prjP (embP z) = some z) →
      ∀ (S : PTr s → Bool), ProverLaw s S →
        ∀ (i : ℕ) (ph ph' : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s)
            (RTs : RootsOfChain lam s) (front : List (Rec lam W.K L C.t)),
          RunsIn C.tr (recomputeChain (K := W.K) C.t C.cms C.x C.salt C.rtreq s A ws embP i ph rts pls)
            (some (ρ, RTs, ph')) →
          PrevOK C i ph front → LateInv C i ph s A →
          (∀ c, ph'.slotVal = some c → extReq C.tr W.depthReq C.rtreq C.j = some (List.ofFn c)) →
          (∀ pre q a post rest cur τ, C.tr = pre ++ fbE C.t q a :: post → fbE C.t q a ∉ pre →
            Ours C pre q (front ++ rest) cur → LateIs (fun k => lateInstancePart L k C.x) i rest cur →
            trOf pre C.t s A ws prjS prjP rest cur = some τ → S (.atV τ) = false →
            S (τ.snoc (chalAt ws τ a.1)) = false) →
          S (PTr.empty s) = false → S (.full (trStar C.tr s A ws prjS RTs pls ρ)) = false
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h0 => h0
  | r :: s, (a, A), (w, ws), prjS, prjP, embP, hprj, S, hP, i, ph, ph', rts, (pl, pls), (c, ρ), (rt, RTs), front, hrun, hprev, hinv, hfin, hES, h0 => by
      obtain ⟨cur, ans, ph₁, rts', hv, hmem, rfl, hrun'⟩ := runsIn_chainB_cons hrun
      obtain ⟨pre, post, htr, hnew⟩ := List.eq_append_cons_of_mem hmem
      obtain ⟨hours, hprev', hrec⟩ := step_rooted C hM hF hv hprev htr hnew
        (fun c hc => hfin c (slotVal_of_chainB s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs c hc hrun'))
      obtain ⟨hk, -, hshd, hown⟩ := hv.fields
      have hroots : ∀ tr' : Tc W, RecIn tr' (cur, ans) →
          ∀ c, rt.1 = some (some c) ∨ rt.2 = some (some c) → (evM lam W.K L).OccursIn tr' c := by
        intro tr' h c hc
        rcases hc with hc | hc
        · exact (roots_occur h).1 (some c, _) c
            (by rw [show ((cur, ans) : Rec lam W.K L C.t).1.shd = cur.shd from rfl, hshd, hc]; rfl)
            rfl
        · exact (roots_occur h).2 (some c, _) c
            (by rw [show ((cur, ans) : Rec lam W.K L C.t).1.own = cur.own from rfl, hown, hc]; rfl)
            rfl
      -- the message of this round is the same, read before any later query of the chain or at the
      -- end
      have hmsg : ∀ (pre' : Tc W) (q' : FbIn lam L C.t) (a' : FsAns lam W.K) (post' : Tc W), C.tr =
            pre' ++ fbE C.t q' a' :: post' →
          RecIn (pre' ++ [fbE C.t q' a']) (cur, ans) →
          msgOf pre' w (fun p => prjS (.inl p)) prjP cur =
            some (msgStar C.tr w (fun p => prjS (.inl p)) rt pl) := by
        intro pre' q' a' post' h1 h2
        rw [msgOf_of_fields pre' w _ hprj hk hshd hown]
        exact congrArg some
          (msgStar_congr w _ pl fun c hc d j => extLeaf_before h1 hM (hroots _ h2 c hc) d j)
      -- the state is 0 after the prover message, and stays 0 after the verifier message
      have hA : S (.atV (Sum.inl (msgStar C.tr w (fun p => prjS (.inl p)) rt pl))) = false :=
        hP (Sum.inl ()) _ h0
      have hB : S (PTr.cons (msgStar C.tr w (fun p => prjS (.inl p)) rt pl)
              (w.chal ans.1) (PTr.empty s)) = false :=
        hES pre cur.q ans post [] cur (Sum.inl _) htr hnew
          (by rw [List.append_nil]; exact hours) (hv.late_eq hinv)
          (by
            show (msgOf pre w (fun p => prjS (.inl p)) prjP cur).map Sum.inl = _
            rw [hmsg pre _ ans post htr hrec]
            rfl) hA
      refine stays0 C hM hF s A ws (fun p => prjS (.inr p))
        (fun z => (prjP z).bind PlainPart.tail?) (fun z => embP (.inr z))
        (fun z => by
          show (prjP (embP (.inr z))).bind PlainPart.tail? = some z
          rw [hprj]; rfl)
        (fun τ => S (PTr.cons (msgStar C.tr w (fun p => prjS (.inl p)) rt pl) (w.chal ans.1) τ))
        (hP.tail _ _) (i + 1) ph₁ ph' rts' pls ρ RTs
        (front ++ [(cur, ans)]) hrun' hprev' (hv.lateInv hinv) hfin ?_ hB
      intro pre' q' a' post' rest cur' τ htr' hnew' hours' hlate' hτ hL
      have hin : RecIn pre' (cur, ans) := ours_recIn C hours' (cur, ans) (by simp)
      refine hES pre' q' a' post' ((cur, ans) :: rest) cur' (Sum.inr (_, w.chal ans.1, τ))
        htr' hnew' (by simpa using hours') ⟨hv.late_eq hinv, hlate'⟩ ?_ hL
      show (msgOf pre' w (fun p => prjS (.inl p)) prjP cur).bind _ = _
      rw [hmsg pre' q' a' post' htr' (hin.mono (List.subset_append_left _ _))]
      show (trOf pre' C.t s A ws _ _ rest cur').map _ = _
      rw [hτ]
      rfl

/-! ## Part 2. One protocol -/

/-- A protocol of the scheme as a `Lane` of the analysis. State is its state function, xout reads
the request that the chain holds so far (`lastX`, Compile/Batch/Rooted.lean) back as an instance,
and extY gives the external oracles that a trace determines under the roots of a first query. -/
def laneOf (W : QueryLayout lam L) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)) (ε : Err Q.loc.shape)
    (State : E.Str → Y → PTr Q.loc.shape → Bool) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) : Lane W where
  t := t
  s := Q.loc.shape
  A := Q.ann
  ws := ws
  prjS := prjS
  prjP := prjP
  ε := ε
  state := fun tr cms xo => (xout xo).map (State (extY tr cms))

theorem extReq_mod {K : ℕ} (tr : Trace (spec lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extReq tr d c (j % 2 ^ d) = extReq tr d c j := by
  unfold extReq
  rw [posOf_congr d (Nat.mod_mod j (2 ^ d))]

/-- A state function that is given, at each place of a transcript, the instance that the chain has
taken in there: inst i from the prover message of round i up to the verifier message of round i. -/
def swSt {Y : Type} {s : Shape} (S : Y → PTr s → Bool) (inst : ℕ → Y) : PTr s → Bool
  | .atV τ => S (inst τ.idx) (.atV τ)
  | .atP τ => S (inst (τ.idx - 1)) (.atP τ)
  | .full τ => S (inst (s.length - 1)) (.full τ)

theorem swSt_empty {Y : Type} {s : Shape} (S : Y → PTr s → Bool) (inst : ℕ → Y) :
    swSt S inst (PTr.empty s) = S (inst 0) (PTr.empty s) := by
  cases s <;> rfl

theorem swSt_snoc {Y : Type} {s : Shape} (S : Y → PTr s → Bool) (inst : ℕ → Y)
    (τ : AtV s) (c : τ.round.Chal) :
    swSt S inst (τ.snoc c) = S (inst τ.idx) (τ.snoc c) := by
  have hd := AtV.done_snoc τ c
  cases hν : τ.snoc c with
  | atP τ' =>
    rw [hν] at hd
    show S (inst (τ'.idx - 1)) _ = _
    rw [show τ'.idx = τ.idx + 1 from hd]
    rfl
  | atV τ' => exact absurd hν (AtV.snoc_ne_atV τ c τ')
  | full τ' =>
    rw [hν] at hd
    show S (inst (s.length - 1)) _ = _
    rw [show s.length = τ.idx + 1 from hd]
    rfl

/-- Outside E_M, E_F and the protocol's state event, if the compiled verifier of a slot accepts and
all its queries are in the trace, then the statement that consists of x and of the extracted
external strings is in the language (under the further hypotheses below). Among these: inst i is the
instance that the chain has taken in with the query of round i (`hx`; `instX`,
Compile/Batch/LateX.lean); and the laws of the state function are asked along this sequence, only
for the false statement x:
(`hst1`) it starts in state 0 of inst 0;
(`hst2`) a prover message of round i leads from state 0 of inst (i - 1) to state 0 of inst i;
(`hst3`) at the end state 0 of the last instance means that x is rejected. -/
theorem mem_of_accepted (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop} (State : E.Str → Y → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε State xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (inst : ℕ → Y)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1)) (.atP τ) = false → State y (inst τ.idx) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y τ, ¬ Lg x y → State y (inst (Q.loc.shape.length - 1)) (.full τ) = false →
      Q.loc.accept x y τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE W.depthReq cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : Lg x (extY tr cms) := by
  by_contra hL
  letI := wq.decO
  letI := wq.ext.dec
  unfold verifyB recomputeChainOfProof afterB at hrun
  obtain ⟨r, hr, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases r with
  | none => cases runsIn_pure_iff.1 h2
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    dsimp only at h2
    split at h2
    · rename_i a b ha hb
      split at h2
      · rename_i hcond
        rw [bind_eq] at h2
        obtain ⟨ok, hok, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
        have hkey : (∀ c, ph.slotVal = some c →
              RunsIn tr (reqCheck (K := W.K) (L := L) W.depthReq π.rtreq π.slot π.path c) true) ∧
            ok = true ∧
            Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
                (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens) = true := by
          cases hsv : ph.slotVal with
          | none =>
            simp only [hsv] at h3
            obtain ⟨y, hy, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
            have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h4)
            exact ⟨fun c hc => (by cases hc), (Bool.and_eq_true_iff.1 h5.1).1, h5.2⟩
          | some c =>
            simp only [hsv] at h3
            rw [bind_eq] at h3
            obtain ⟨y, hy, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
            have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h4)
            obtain ⟨h6, rfl⟩ := Bool.and_eq_true_iff.1 h5.1
            exact ⟨fun c' hc' => (by cases hc'; exact hy), h6, h5.2⟩
        obtain ⟨hreq, rfl, hacc⟩ := hkey
        -- the slot value is under the request root
        have hfin : ∀ c,
            ph.slotVal = some c → extReq tr W.depthReq π.rtreq π.slot = some (List.ofFn c) :=
          fun c hc => (extReq_of_check hM (hreq c hc)).2
        -- the state stays 0 along the chain
        let C : Ctx W := ⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩
        have hbad : State (extY tr cms) (inst (Q.loc.shape.length - 1))
              (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)) = false :=
          stays0 C hM hF Q.loc.shape Q.ann wq.sh prjS prjP embP
            hprjP (swSt (State (extY tr cms)) inst)
            (fun τ m h => by
              show State (extY tr cms) (inst (τ.snoc m).idx) _ = false
              rw [AtP.idx_snoc]
              exact hst2 _ τ m hL h) 0 .first ph π.roots π.plains ρ rts []
            hr ⟨rfl, rfl⟩
            (fun n hl hxn _ => ⟨(hlate n hl hxn).1, Or.inl ⟨rfl, rfl⟩, (hlate n hl hxn).2⟩) hfin
            (fun pre q a post rest cur τ htr hnew hours hlt hτ hl => by
              by_contra hn
              have hidx : τ.idx = rest.length := idx_trOf pre _ _ _ _ _ rest cur τ hτ
              have hn' : State (extY tr cms) (inst rest.length) (τ.snoc (chalAt wq.sh τ a.1)) =
                  true := by
                rw [swSt_snoc, hidx] at hn
                simpa using hn
              have hl' : State (extY tr cms) (inst rest.length) (.atV τ) = false := by
                rw [← hidx]; exact hl
              have hy : extY pre cms = extY tr cms := hstab pre q a post htr (ours_cms C a hours)
              have hfl : (laneOf W t Q wq.sh prjS prjP ε State xout extY).flips
                  pre cms (lastX C.xo rest cur) rest cur a :=
                ⟨State (extY tr cms) (inst rest.length), τ, by
                  show (xout (lastX ((xin x).map L.early) rest cur)).map (State (extY pre cms)) = _
                  rw [lastX_of_lateIs (xin x) rest cur hlt, hx, hy]; rfl, hτ, hl', hn'⟩
              rw [List.nil_append] at hours
              rcases hours with ⟨h1 | h1, rfl⟩ | ⟨slot, sh, c, sd, h1, h7, h8, h9, h10⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · obtain rfl : rest = (slotTr sd sh q).1 := (congrArg Prod.fst h10).symm
                obtain rfl : cur = (slotTr sd sh q).2 := (congrArg Prod.snd h10).symm
                have e3 : sd.x = C.xo := h9
                refine hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1,
                    π.slot % 2 ^ W.depthReq, Nat.mod_lt _ (Nat.pow_pos (by decide)), π.rtreq, c, sd,
                    digOf_ofFn _, by rw [extReq_mod]; exact h7, h8, ?_⟩
                rw [e3]
                exact hfl)
            (by rw [swSt_empty]; exact hst1 _ hL)
        have hall : ∀ c ∈ a ++ b,
            c.wellFormed = true ∧ RunsIn tr (runCheck (K := W.K) c) true := fun c hc =>
          ⟨(Bool.and_eq_true_iff.1 (List.all_eq_true.1 hcond.2 c hc)).1,
            runsIn_runCheck_of_runChecks _ hok c hc⟩
        -- the oracle-level verifier accepts
        have heq := hloc x (wq.ext.build fun p => (π.ext p).map Opening.sym) (extY tr cms)
          (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens)
          (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)
          (by rw [mkTr_rho, trStar_rho]) (by rw [mkTr_plains, trStar_plains tr _ _ hco])
          (fun p hp => by
            rw [mkTr_rho] at hp
            obtain ⟨op, hop, hmem⟩ := mem_checksExt
              wq.ext embE cms _ π.ext wq.ext.all b hb p (hOK.ext.complete p) (decide_eq_true hp)
            obtain ⟨hwf, hrc⟩ := hall _ (List.mem_append_right _ hmem)
            rw [hOK.ext.build_rd _ p op.sym (by rw [hop]; rfl)]
            exact (hagree p op.sym op.salt (extLeaf_of_check _ hM hwf hrc)).symm)
          (fun p hp => by
            rw [mkTr_rho, mkTr_plains] at hp
            exact read_mkTr_eq hM Q.loc.shape Q.ann hco wq.sh hOK.sh embS prjS
              hprjS rts _ π.opens a ha
              (fun c hc => hall c (List.mem_append_left _ hc)) π.plains ρ p (decide_eq_true hp))
        rw [heq, hst3 _ _ hL hbad] at hacc
        cases hacc
      · cases runsIn_pure_iff.1 h2
    · cases runsIn_pure_iff.1 h2

/-! ## Part 3. The three protocols, the event Bad, and the theorem -/

section StOf
variable {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (ε : Err Q.shape)

open Classical in
/-- The canonical state function of a round-by-round sound IOP: 0 where the prover has lost
(Iop/State.lean). -/
def stOf : E.Str → Y → PTr Q.shape → Bool := fun y x τ =>
  decide (¬ Lost Q.shape ε (fun τ => Q.accept x y τ = false) τ)

variable {Q ε}

theorem stOf_eq_false {y : E.Str} {x : Y} {τ : PTr Q.shape} :
    stOf Q ε y x τ = false ↔ Lost Q.shape ε (fun τ => Q.accept x y τ = false) τ := by
  simp [stOf]

theorem stOf_eq_true {y : E.Str} {x : Y} {τ : PTr Q.shape} :
    stOf Q ε y x τ = true ↔ ¬ Lost Q.shape ε (fun τ => Q.accept x y τ = false) τ := by
  simp [stOf]

theorem stOf_start {Lg : Y → E.Str → Prop} (h : Q.Sound Lg ε) (y : E.Str) (x : Y) (hL : ¬ Lg x y) :
    stOf Q ε y x (PTr.empty Q.shape) = false :=
  stOf_eq_false.2 ((lost_empty _ _ _).2 (h x y hL))

theorem stOf_prover (y : E.Str) (x : Y) : ProverLaw Q.shape (stOf Q ε y x) :=
  fun τ m h => stOf_eq_false.2 (Lost.prover _ _ _ τ m (stOf_eq_false.1 h))

theorem stOf_full (y : E.Str) (x : Y) (τ : Tr Q.shape) (h : stOf Q ε y x (.full τ) = false) :
    Q.accept x y τ = false :=
  (lost_full _ _ _ τ).1 (stOf_eq_false.1 h)

theorem stOf_ver (y : E.Str) (x : Y) : VerLaw Q.shape ε (stOf Q ε y x) :=
  fun τ h =>
    le_trans (cnt_mono fun _ hc => stOf_eq_true.1 hc) (Lost.verifier _ _ _ τ (stOf_eq_false.1 h))

end StOf

theorem timesShared_allLocal (N : ℕ) :
    ∀ (s : Shape) (ε : Err s), Err.timesShared N (RoundSplits.allLocal s) ε = ε
  | [], () => rfl
  | _ :: s, (e, ε) => congrArg (Prod.mk e) (timesShared_allLocal N s ε)

/-- The law on verifier messages for an IOP with local rounds only. -/
theorem stOf_joint {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (ε : Err Q.shape) (N : ℕ)
    (y : E.Str) (x : Fin N → Option Y) :
    JointLaw N Q.shape (RoundSplits.allLocal Q.shape) ε fun j => (x j).map (stOf Q ε y) := by
  have h := BatchH4.jointLaw_of_verLaw N Q.shape (RoundSplits.allLocal Q.shape) ε (fun j => (x j).map (stOf Q ε y)) (fun j S hS => by
           obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
           exact stOf_ver y xj)
  rwa [timesShared_allLocal] at h

theorem laneOf_ok {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann}
    {prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)} {ε : Err Q.loc.shape}
    {State : E.Str → Y → PTr Q.loc.shape → Bool} {xout : Option X → Option Y}
    {extY : Tc W → List (Dig lam) → E.Str} {N : ℕ} (hws : RoundsQueryLayout.OKG Q.loc.shape Q.ann ws)
    (hj : ∀ y (x : Fin N → Option Y), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y)) :
    (laneOf W t Q ws prjS prjP ε State xout extY).OK N :=
  ⟨hws, fun pre cms xs => by
    have h := hj (extY pre cms) fun j => (xs j).bind xout
    have e : (fun j => ((xs j).bind xout).map (State (extY pre cms))) =
        fun j =>
          (xs j).bind
              ((laneOf W t Q ws prjS prjP ε State xout extY).state pre cms) := funext fun j => by
      cases xs j <;> rfl
    rw [e] at h
    exact h⟩

open Classical in
/-- read the body of a leaf as the symbol at position p of a prover oracle of the protocol t -/
def prjSym (t : Tag) (p : OPos (shapeOf L t)) : Body L → Option (OSym (shapeOf L t) p)
  | some (.inr ⟨t', z⟩) =>
      if h : t' = t then
        if h2 : (h ▸ z : SymAny (shapeOf L t)).1 = p then
          some (h2 ▸ (h ▸ z : SymAny (shapeOf L t)).2)
        else none
      else none
  | _ => none

theorem prjSym_emb (t : Tag) (p : OPos (shapeOf L t)) (a : OSym (shapeOf L t) p) :
    prjSym t p (some (.inr ⟨t, (⟨p, a⟩ : SymAny (shapeOf L t))⟩)) = some a := by
  simp [prjSym]

/-- For a well-formed wire record (`W.OKG`): a determined leaf of the tree over an encoded index
gives the symbol of the extracted string. -/
theorem extEnc_apply (hW : W.OKG) {tr : Tc W} {cm : Dig lam} {p : Fin L.wordLength} {a : L.Symbol} {sl : Bits}
    (h : extLeaf tr W.depth cm p.val = some ⟨some (.inl a), sl⟩) : extEnc W tr cm p = a :=
  hW.B.ext.build_rd _ p a (by simp only [h])

/-- Outside E_M, the string under a root that occurs before a Fiat-Shamir query, or at it, is the
same before that query and at the end. -/
theorem extEnc_before {tr pre post : Tc W} {t : Tag} {q : FbIn lam L t} {a : FsAns lam W.K}
    (htr : tr = pre ++ fbE t q a :: post) (hM : ¬ EM tr) {cm : Dig lam}
    (hc : (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) cm) :
    extEnc W pre cm = extEnc W tr cm := by
  unfold extEnc
  congr 1
  funext p
  rw [extLeaf_before htr hM hc]

variable (W)

def laneT (ε : Err L.offline.shape) : Lane W :=
  laneOf W Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T.sh (prjSym Tag.test) some ε (stOf L.offline ε)
    (fun _ => some ()) fun tr cms => extEnc W tr (cms.getD 0 default)

def laneL (ε : Err L.link.shape) : Lane W :=
  laneOf W Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk.sh (prjSym Tag.link) some ε (stOf L.link ε)
    (fun _ => some ())
    fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default))

def laneB (ε : Err L.onlineBatch.loc.shape) (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool) :
    Lane W :=
  laneOf W Tag.onl L.onlineBatch W.B.sh (prjSym Tag.onl) some ε State id fun tr cms =>
    extEnc W tr (cms.getD 0 default)

/-- the entry e, after the trace pre, causes the state event for one of the three protocols -/
def stepS (ℓT ℓL ℓB : Lane W) (pre : Tc W) (e : QA (spec lam W.K L)) : Prop :=
  ℓT.step pre e ∨ ℓL.step pre e ∨ ℓB.step pre e

variable {W}

/-- Under the hypotheses below, the answer to one query causes the state event of one of the three
protocols (`stepS`) with probability at most εs: a query belongs to one protocol only. -/
theorem pr_stepS_le {ℓT ℓL ℓB : Lane W} (hT : ℓT.t = Tag.test) (hL : ℓL.t = Tag.link)
    (hB : ℓB.t = Tag.onl) {N : ℕ} (hN : N = 2 ^ W.depthReq) (oT : ℓT.OK N) (oL : ℓL.OK N)
    (oB : ℓB.OK N) {εs : ℝ≥0∞} (bT : Err.Below ℓT.ε εs) (bL : Err.Below ℓL.ε εs)
    (bB : Err.Below ℓB.ε εs) (pre : Tc W) (o : OracleName) (q : domOf lam L o) :
    pr (unif ((spec lam W.K L).Rng o))
        {r | stepS W ℓT ℓL ℓB pre (⟨o, q, r⟩ : QA (spec lam W.K L))} ≤ εs := by
  obtain ⟨tT, sT, AT, wT, pT, qT, eT, stT⟩ := ℓT
  obtain ⟨tL, sL, AL, wL, pL, qL, eL, stL⟩ := ℓL
  obtain ⟨tB, sB, AB, wB, pB, qB, eB, stB⟩ := ℓB
  cases (show tT = Tag.test from hT)
  cases (show tL = Tag.link from hL)
  cases (show tB = Tag.onl from hB)
  cases o
  case fb t =>
    cases t
    · refine le_trans (pr_mono _ ?_) (Lane.pr_step_le _ hN oT bT pre q)
      rintro r (h | h | h)
      · exact h
      · exact absurd (Lane.step_oracle h)
          (fun (h' : OracleName.fb Tag.test = OracleName.fb Tag.link) => by cases h')
      · exact absurd (Lane.step_oracle h) (fun (h' : OracleName.fb Tag.test = OracleName.fb Tag.onl) => by cases h')
    · refine le_trans (pr_mono _ ?_) (Lane.pr_step_le _ hN oL bL pre q)
      rintro r (h | h | h)
      · exact absurd (Lane.step_oracle h)
          (fun (h' : OracleName.fb Tag.link = OracleName.fb Tag.test) => by cases h')
      · exact h
      · exact absurd (Lane.step_oracle h) (fun (h' : OracleName.fb Tag.link = OracleName.fb Tag.onl) => by cases h')
    · refine le_trans (pr_mono _ ?_) (Lane.pr_step_le _ hN oB bB pre q)
      rintro r (h | h | h)
      · exact absurd (Lane.step_oracle h) (fun (h' : OracleName.fb Tag.onl = OracleName.fb Tag.test) => by cases h')
      · exact absurd (Lane.step_oracle h) (fun (h' : OracleName.fb Tag.onl = OracleName.fb Tag.link) => by cases h')
      · exact h
  all_goals
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - (h | h | h) <;> cases Lane.step_oracle h

/-- the instance that the chain of a slot of Batch with the instance x has taken in with the query
of round i -/
def instB (L : BatchProtocol I X) (x : X) (i : ℕ) : X :=
  match L.late with
  | some n => if n ≤ i then x else L.early x
  | none => L.early x

theorem instX_some (L : BatchProtocol I X) (x : X) (i : ℕ) :
    id (instX L (some x) i) = some (instB L x i) := by
  unfold instX instB
  cases L.late with
  | none => rfl
  | some n => by_cases h : n ≤ i <;> simp [h]

section InstB
variable {s : Shape} {A : RoundSplits s} (h0 : ∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n s A)
include h0

theorem instB_zero {x : X} : instB L x 0 = L.early x := by
  unfold instB
  cases hl : L.late with
  | none => rfl
  | some n => simp [Nat.pos_iff_ne_zero.1 (h0 n hl).1]

/-- Under h0: from round j - 1 to round j the instance stays, or j is the round L.late -/
theorem instB_step (x : X) (j : ℕ) :
    instB L x (j - 1) = instB L x j ∨
    (L.late = some j ∧ instB L x (j - 1) = L.early x ∧ instB L x j = x) := by
  unfold instB
  cases hl : L.late with
  | none => exact Or.inl rfl
  | some n =>
    have hn := (h0 n hl).1
    by_cases h1 : n ≤ j - 1
    · exact Or.inl (by simp [h1, show n ≤ j by omega])
    · by_cases h2 : n ≤ j
      · obtain rfl : n = j := by omega
        exact Or.inr ⟨rfl, by simp [h1], by simp⟩
      · exact Or.inl (by simp [h1, h2])

theorem instB_last {x : X} : instB L x (s.length - 1) = if L.late.isSome then x else L.early x := by
  unfold instB
  cases hl : L.late with
  | none => rfl
  | some n =>
    have := (h0 n hl).2.lt_length
    simp [show n ≤ s.length - 1 by omega]

end InstB

/-- Soundness of the compilation with shared rounds, with Test and Link, for a wire record whose
rounds may have proof-of-work bits. -/
theorem bcsSoundBatchG : Spec.bcsSoundBatchG := by
  intro I X lam L W Rno εs hS hlT hlL hlB hco hW
  obtain ⟨εT, hbT, hsT⟩ := hS.sndT
  obtain ⟨εL, hbL, hsL⟩ := hS.sndL
  obtain ⟨εB, hbB, hB0, State, hB1, hB2, hBs, hB3, hB4⟩ := hS.sndB
  have oT : (laneT W εT).OK L.maxBatchSize := laneOf_ok hW.T.sh (stOf_joint L.offline εT L.maxBatchSize)
  have oL : (laneL W εL).OK L.maxBatchSize := laneOf_ok hW.Lk.sh (stOf_joint L.link εL L.maxBatchSize)
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  refine ⟨fun tr =>
      (EM tr ∨ EF tr) ∨ StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) tr,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β A t hA
    have h := pr_stepEvent_le (S := spec lam W.K L)
      (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) (fun _ => εs)
      (fun pre e he hs =>
        hs.elim (fun h1 => h1.1 he) fun h1 => h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      (fun pre o q _ => pr_stepS_le rfl rfl rfl hW.slots oT oL oB hbT hbL hbB pre o q) A t hA
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    calc
      pr A.withTrace.law
            {o | (EM o.2 ∨ EF o.2) ∨
              StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} ≤
          pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr A.withTrace.law
              {o | StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
      _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
          rw [add_comm]
          gcongr
          exact Nat.le_succ t
  · rintro tr tr' ((h | h) | h)
    · exact Or.inl (Or.inl (h.append tr'))
    · exact Or.inl (Or.inr (h.append tr'))
    · exact Or.inr (StepEvent.append h tr')
  · intro tr cm π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T _ id (fun _ => none)
      (fun s => some (.inl s)) hW.T hlT
      (Iop.BatchOne.BAnn.allLocal_coherent _) (Lg := fun _ y => L.decodeIndex y ≠ none) (stOf L.offline εT)
      (prjSym Tag.test) (fun p a => prjSym_emb Tag.test p a) some (fun _ => rfl) (fun _ => some ())
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εT hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl h2⟩)) [cm] () π
      (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h) (fun y hL => stOf_start hsT y () hL)
      (fun y τ m _ h => stOf_prover y () τ m h) (fun y τ _ h => stOf_full y () τ h) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        rw [hW.extDepth.1, (hW.extT p).1, (hW.extT p).2] at h
        exact extEnc_apply hW h)
  · intro tr cm cm' π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk _ id (fun _ => none)
      (fun s => some (.inl s)) hW.Lk hlL
      (Iop.BatchOne.BAnn.allLocal_coherent _)
      (Lg := fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) (stOf L.link εL)
      (prjSym Tag.link) (fun p a => prjSym_emb Tag.link p a) some (fun _ => rfl) (fun _ => some ())
      (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default)))
      εL hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inl h2)⟩))
      [cm, cm'] () π
      (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h) (fun y hL => stOf_start hsL y () hL)
      (fun y τ m _ h => stOf_prover y () τ m h) (fun y τ _ h => stOf_full y () τ h) hrun
      (fun pre q a post htr hocc =>
        Prod.ext (extEnc_before htr hM (hocc _ (by simp)))
          (extEnc_before htr hM (hocc _ (by simp))))
      (fun p a sl h => by
        rw [hW.extDepth.2.1] at h
        cases p with
        | inl p =>
          rw [(hW.extL.1 p).1, (hW.extL.1 p).2] at h
          exact extEnc_apply hW h
        | inr p =>
          rw [(hW.extL.2 p).1, (hW.extL.2 p).2] at h
          exact extEnc_apply hW h)
  · intro tr cm x π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.onl L.onlineBatch W.B _ id some (fun s => some (.inl s)) hW.B hlB hco
      (Lg := fun x y => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x) State
      (prjSym Tag.onl) (fun p a => prjSym_emb Tag.onl p a) some (fun _ => rfl) id
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εB hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inr h2)⟩)) [cm] x π
      (instB L x) (instX_some L x) (fun n hn _ => hB0 n hn)
      (fun y hL => by rw [instB_zero hB0]; exact hB1 y x hL)
      (fun y τ m hL h => by
        rcases instB_step hB0 x τ.idx with h1 | ⟨h1, h2, h3⟩
        · rw [h1] at h; exact hB2 y _ τ m h
        · rw [h2] at h; rw [h3]; exact hB2 y x τ m (hBs y x τ hL h1 h))
      (fun y τ hL h => hB3 y x τ hL (by rw [← instB_last hB0]; exact h)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        rw [hW.extDepth.2.2, (hW.extB p).1, (hW.extB p).2] at h
        exact extEnc_apply hW h)
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)

end Compile.Batch
