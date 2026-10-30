-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ItemRightOf.lean: CONDITIONAL.

Not shown here. THAT RightFoot HOLDS ANYWHERE: every field of it is a hypothesis HERE; no example is
known. Laws for some of them lie in other files; none of these is called here: cells, makers, rows,
terms, own and the first half of back (Law/W/FootAtStand.lean pays them at a state behind the
member's step), idn and hot (Law/W/IdnHead.lean, Law/W/HotStand.lean: AT THE LIBRARY's FULL SIZE
ALONE AND AT THE FORMAT's EARLIER HASH ALONE). For emb the one law that lies (`emb_at` below) stands
AT THE LIBRARY's OWN SIZES ALONE and under a hypothesis on the witness. Of back's second half: the
batched sumcheck's own claim: `stack_led` (Law/StackLed.lean), under the start; of the start's four
sentences (Law/StackStart.lean) the lookup's join has no law but at the full size; the merge's own
claim: Law/OwnAtStand.lean, under its start. K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE
LIBRARY's ELEVEN SWITCHES: at every other shape k4Right_of says nothing. TWO FIELDS TIE ONE LETTER:
cells ties the matrices Mm to the input's cells off the planes' matrix; look ties the planes' matrix
in Mm to what the lookup's side holds. k4Right_of HAS SEVEN HYPOTHESES, K4Front's open sentences
among them. AT A THREAD NONE OF WHOSE STEPS ACCEPTS, K4Foot AND K4Right HOLD EMPTILY. By a walk
of import lines the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass,
CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or
Johnson/D/; under Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on
soundness, on completeness or on any other property. No property is claimed.

The door from the laws of the right half into `ItemRight` and `K4Right` (Law/W/SlotsOfStand.lean).
At one state: ten of the fourteen fields of OpenedRight by `right_join` (Law/W/RightAll.lean) from
`right_norms` and `right_gated`; the field look by `look_of_asks` (Johnson/Road/K4/W/LookAsks.lean),
its two public clauses by `lookAsks_of_left` (W/LookCols.lean). At the thread: the ties to what the
verifier holds by Law/PtsAtStand.lean; the public facts on the layout by `kept_ground`; the numbers
by `gatedNums_of_plan` and `normsPlan_of_plan` (Johnson/Road/K4/C/); the two tensors by
`gated_tensors`; the gated products' tables and the cubes' fits by `gated_run`, `gated2_run`
(Law/SumAtRun.lean). That the features of the streams' limbs and of the two gated tensors lie inside
their matrices: from K4Plan, by `streamsIn_of_plan` (C/StreamsOf.lean, inside normsPlan_of_plan) and
`gatedIn_of_plan` (C/GatedInPlan.lean).

  `RightFoot h D tl P Q o F₀ F₁ mask Mm w hh ds seen`   what is left as a hypothesis at one state:
      ten fields; emb, terms, idn, hot, own, back in the very texts of the fields that they feed.
  `itemRight_of`   ItemRight from RightFoot, the ties and the public facts.
  `tabs_at`   the gated products' tables are there and the cubes' sizes fit, at a state behind the
      member's step: from the public test k4Fits.
  `emb_at`   the field emb at such a state, by the one law that lies for it.
  `K4Foot T At b …`   RightFoot at every state behind the member's step.
  `k4Right_of`   K4Right from K4Foot.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SlotsOfStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightAll
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnFits
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts
import Johnson.Desc.ProofFile.Honest.K4.Law.LookSkel
import Johnson.Road.K4.W.KeptGround
import Johnson.Road.K4.W.LookCols
import Johnson.Road.K4.W.HotEmb
import Johnson.Road.K4.C.GatedNums
import Johnson.Road.K4.C.NormsPlanOf
import Johnson.Road.K4.C.GatedInPlan
import Johnson.Road.K4.C.GatedCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own Ten ClaimEnv downFrom)
open OnBytes.Road (sclOf cellsOf cellsAt pt gl_numerals SizedW admitted_of_layout)
open OnBytes.Road.K4 (kept_atS entryTrue)
open OnBytes.Road.K4.W (K4Plan K4Ground IdnHold HotPoint OwnFront OwnBack LookLeft lookAsks_of_left
  look_of_asks kept_env kept_ground ground holds_item EmbCube uEOf)
open OnBytes.Road.K4.C (CellsAre NormsPlan RowFields GatedIn GatedNums gated_tensors
  gatedNums_of_plan normsPlan_of_plan gatedIn_of_plan)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim embR xS)
open Meaning.Emb (EmbNums)
open VerifiableInference.Desc (Block Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **What is left as a hypothesis at one state.** The letters are ItemRight's. This defines a
hypothesis; the definition claims nothing. -/
structure RightFoot (h : Layer.Shape) (D : Dim) (tl : HTailF2) (P : Layer.Pub) (Q : K4Pub)
    (o : Own) (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In)
    (hh ds : List Fmt.Drawn) (seen : Seen) : Prop where
  /-- the matrices hold the input's cells, off the planes' matrix -/
  cells : CellsAre Q w Mm
  /-- the norms: the honest side's functions return; three sizes -/
  makers : MakersNorms Q w hh ds o D
  /-- the norms' rows' fields read as the library's -/
  rows : RowFields Q w (ptsOf Q w (hh ++ ds.take (rowsRound Q.P Q.g))) D
    (cellsOf D (cellsAt o.v.y Mm))
  /-- the field emb of OpenedRight, in its own text -/
  emb : o.v.g = 0 → Reading.gl.val (wEmb Q w hh ds) =
    ∑ kh ∈ Finset.range (o.v.y.h.d / o.v.y.S2),
      Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
        ∑ r ∈ Finset.range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
          Blocks.ext D.lT
            (fun p => xS D (cellsOf D (cellsAt o.v.y Mm)) 0 (kh * 2 ^ o.v.y.ls + r) p)
            (uEOf Reading.gl o.v o.H)
  /-- the fields rt, sc, sel of OpenedRight -/
  terms : RightTerms (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) Q o w hh ds
  /-- the norms' identities at the cells -/
  idn : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
  /-- the selector's identity, extended over the positions, at the lookup's token point -/
  hot : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)
  /-- the own claims of four sumchecks -/
  own : ∀ sh, ((Array.range (4 * P.y.NI)).mapM fun i => F₀.shown (o.H.tV.sEnd + i)) = some sh →
    OwnFront Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o sh
  /-- what is left of what the lookup's three claims ask -/
  look : LookLeft tl o F₀ mask Mm
  /-- behind "back": the right half at its two slots, and the two own claims -/
  back : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    OpenedRightBack (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) Q o w hh ds seen ∧
      OwnBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o

/-- **ItemRight FROM RightFoot, THE TIES AND THE PUBLIC FACTS.** CONDITIONAL: on every hypothesis
named. -/
theorem itemRight_of {h : Layer.Shape} {pc : List (List String)} {D : Dim} {tl : HTailF2}
    {P : Layer.Pub} {Q : K4Pub} {o : Own} {F₀ F₁ : Fork} {mask : ℕ → Cb.Gl.E}
    {Mm : Road.Mats Cb.Gl.E} {w : K4In} {hh ds : List Fmt.Drawn} {seen : Seen}
    {rd : Layer.Reads} {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    {pts : List (String × Array E)} {rows : Bool} {g : ℕ} {fs : Array Aff}
    (Gr : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) (hy : Q.P.y = o.v.y)
    (Ng : GatedNums Q D) (Np : NormsPlan Q D) (Gi : GatedIn Q.P.y)
    (hfr : formsFrontWith rows P g o F₀ = some (fs, F₁)) (Ap : PtsAre Q w hh ds o)
    (Ag : ∃ tb1 tb2, GatedAt Q w hh ds o tb1 tb2)
    (Ft : RightFoot h D tl P Q o F₀ F₁ mask Mm w hh ds seen) :
    ItemRight h D tl P Q o F₀ F₁ mask Mm w hh ds seen := by
  letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
  have Ad := admitted_of_layout Gr.lay Gr.sw.p3
  have Sw : OnBytes.Road.Switches o.v.y.h := by rw [Ad.shape]; exact Gr.sw
  obtain ⟨Z1, ZV, _, _, F, _⟩ := ground Gr gl_numerals Mm (holds_item Gr Mm F₁ mask)
  obtain ⟨ts, tu, hts, htu, Ss, Su⟩ :=
    gated_tensors F hy Ad.laid Sw Ft.cells Np.mats Gi
  obtain ⟨tb1, tb2, Ag⟩ := Ag
  exact
    { right := right_join (right_norms Ap Ft.makers F hy Ft.cells Np Ft.rows)
        (right_gated Ag hts htu Ss Su Ng) Ft.emb Ft.terms
      idn := Ft.idn
      hot := Ft.hot
      own := Ft.own
      look := look_of_asks hfr Gr (lookAsks_of_left Gr Ft.look)
      back := Ft.back }

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **The gated products' tables are there and the cubes' sizes fit, at a state behind the member's
step**: from the public test k4Fits (K4Seated's field fits), by `gated_run` and `gated2_run`
(Law/SumAtRun.lean). CONDITIONAL: on Z, hT and hd. -/
theorem tabs_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true) :
    ∃ tb1 tb2, gatedTabs Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb1 ∧
      gatedTabs2 Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb2 ∧
      (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom (pts5 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).rs
            (Q.P.y.h.ll + Q.P.y.lPf) ++
          ztOf Q (pts5 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds))
        tb1).cube.fits = true ∧
      (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        ((pts6 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).rhoM ++
          downFrom (pts6 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).rs
            Q.P.y.lfe ++
          (pts6 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).rt)
        tb2).cube.fits = true := by
  have Se := Z.seat
  have hk : k4Fits Q (look Q m.st.heard) (tokens m.st.input.x) = true :=
    Se.fits m.st.heard m.st.input hT.2.1 hT.2.2.2.2.2.2
  have hr := stand_reach Z
  obtain ⟨_, _, _, _, e4, e5, e6⟩ := k4StartAt_eq Q
  have l6 : rE Q.P Q.hp Q.g + 1 ≤ ds.length := by rw [← e6]; exact hr
  have l5 : rJ6 Q.P Q.hp Q.g ≤ ds.length := by
    unfold rE at l6
    omega
  have l4 : rJ5 Q.P Q.hp Q.g ≤ ds.length := by
    unfold rJ6 at l5
    omega
  have hh := k4_heard_front Se hT
  have tk : ∀ n, (m.st.heard ++ ds.take n).take Q.r0 = m.st.heard := by
    intro n
    rw [← hh]
    exact List.take_left
  have ln : ∀ n, n ≤ ds.length → ((m.st.heard ++ ds.take n).drop Q.r0).length = n := by
    intro n hn
    rw [k4_own_drop Se hT, List.length_take]
    exact Nat.min_eq_left hn
  have s4 : (starts Q).getD 4 0 = rJ5 Q.P Q.hp Q.g := by rw [k4_starts]; rfl
  have s5 : (starts Q).getD 5 0 = rJ6 Q.P Q.hp Q.g := by rw [k4_starts]; rfl
  obtain ⟨tb1, t1, f1⟩ := gated_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ5 Q.P Q.hp Q.g)) (k4_own_fits Se hT hd _)
    (by rw [ln _ l4, s4]) (by rw [tk]; exact lookSkel_refl _)
  obtain ⟨tb2, t2, f2⟩ := gated2_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g)) (k4_own_fits Se hT hd _)
    (by rw [ln _ l5, s5]) (by rw [tk]; exact lookSkel_refl _)
  exact ⟨tb1, tb2, t1, t2, f1, f2⟩

/-- **The field emb, at a state behind the member's step, BY THE ONE LAW THAT LIES FOR IT**
(`right_emb`, Law/W/RightGated.lean): AT THE LIBRARY's OWN SIZES ALONE, and under the identity j11
at every feature and position, a hypothesis on the witness. CONDITIONAL: on every hypothesis
named. -/
theorem emb_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {h : Layer.Shape} {D : Dim} {Mm : Road.Mats Cb.Gl.E}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hlT : D.lT = o.v.y.h.lt) {ce : ClaimEnv} {cl : WsClaim} {un : WsUnit}
    (env : claimEnvOf Q (ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) =
      some ce)
    (claim : ce.claimE (ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).ZE
      (ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).tkh Q.P.V
      (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = some cl)
    (hu : Q.P.wsLay.U[cl.ui]? = some un) (hs : wsClaimShape Q.P.wsLay cl = .ok ()) (sh : WsShape)
    (Zs : SizedW sh ppref) (hl : wsLayOf sh true kRef = .ok Q.P.wsLay) (hV : Q.P.V = ppref.V)
    (Ne : EmbNums o.v.y) (hZ : o.H.ZE.size = o.v.y.ls + o.v.y.h.lt)
    (hk : o.H.tkh.size = o.v.y.lPd - o.v.y.ls)
    (hJ : EmbCube (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
      (embR ppref kRef (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w))
      (fun i => (k4Wit Q cells weights tokens (look Q) m.st.input).tokv.getD i 0) o.v.y.h.d) :
    o.v.g = 0 → Reading.gl.val (wEmb Q (k4Wit Q cells weights tokens (look Q) m.st.input)
       m.st.heard ds) =
      ∑ kh ∈ Finset.range (o.v.y.h.d / o.v.y.S2),
        Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
          ∑ r ∈ Finset.range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
            Blocks.ext D.lT
              (fun p => xS D (cellsOf D (cellsAt o.v.y Mm)) 0 (kh * 2 ^ o.v.y.ls + r) p)
              (uEOf Reading.gl o.v o.H) := by
  intro h0
  obtain ⟨_, _, _, _, eg, _⟩ := stand_led Z
  letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
  exact right_emb (embAt_at Z hT (beq_iff_eq.mpr (eg.symm.trans h0)) _ env claim) hu hs sh Zs hl
    hV Ne hZ hk hlT hJ h0

/-- **RightFoot AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
The binders are K4Right's. This defines a hypothesis; the definition claims nothing. -/
def K4Foot (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    RightFoot h D tl p.P Q o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))

/-- **K4Right FROM K4Foot.** hAt: the states that are meant are states of the structure Thread's
proposition Thr. CONDITIONAL: on every hypothesis named. -/
theorem k4Right_of
    {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
    {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim}
    {St : Stated} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2}
    {p : Par} {h : Layer.Shape} {pc : List (List String)} {D : Dim}
    (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4Foot T At b cells weights tokens look Q M own rdOf tl p h D) :
    K4Right T At b cells weights tokens look Q M own rdOf tl p h D := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  have Se := hSeat blk hblk
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  obtain ⟨_, _, Ak⟩ := (hF blk hblk k s m E ds y cols s' hA hd hS ds').asks
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' Aq o :=
    ⟨Se, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  have hT := hAt k s m E hA
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨_, vy⟩ := kept_env (kept_atS hdec) A ho
  obtain ⟨r, pts, Gr⟩ := kept_ground (kept_atS hdec) A ho
  have hy : Q.P.y = o.v.y := by rw [← eP]; exact vy.symm
  have AQ : K4Plan h pc Q.P Q.g tl D := by rw [← eP, ← eg]; exact A
  obtain ⟨tb1, tb2, t1, t2, f1, f2⟩ := tabs_at Z hT hd
  exact itemRight_of Gr hy (gatedNums_of_plan AQ) (normsPlan_of_plan AQ) (gatedIn_of_plan AQ) hf
    (ptsAre_at Z hT _) ⟨tb1, tb2, gatedAt_at Z _ t1 t2 f1 f2⟩
    (hR blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.itemRight_of
#print axioms ProofFile.Honest.K4.W.tabs_at
#print axioms ProofFile.Honest.K4.W.emb_at
#print axioms ProofFile.Honest.K4.W.k4Right_of
