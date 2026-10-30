-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchAtHead.lean: THE BATCHING MEMBER OF EACH OF THE 25 LINKS of the proof
file's own first chain, under the head at which the library's laws on that chain speak (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): FROM THE LAWS OF THE LINK's RUNS OF CLAIMS (RunsLaw,
Johnson/Desc/First/Batch/Shape/BatchFold.lean) to the seated member's own decision. A joining of
laws; nothing is evaluated.

  `order_places`: every run of the three orders stands at a hearing member number 1 to 8, of a kind
    other than K9 and K10.
  `run_guarded`: so, at the seat, a run that the order names is a guarded run: it returns only where
    the reply stayed.
  `Kept`; `fold_keeps`, `set_out`, `batch_keeps`: the gathering and the bare batching keep the
    reply, where every run does.
  `batchGS`: batchG (BatchMember.lean), and no mark of failure on the shape BEHIND.
  **`batch_named`** (l < 25): Lk by cF.links[l]? · p by IM.k9At Zp l · w by K9.testsWhere Zp.p.X l 0
    · the member by its number 14 l + Lk.hear.length + 2 in the flat list · Lk.order = orderOf
    (subAt l): FOR EVERY RunsLaw R OF Lk.hear AND Lk.order: batchGS p.rows w.1 ‹R's runs on shapes›
    Lk.order returns u at chainSh s · the round has drawn just one element · the ledger is empty ·
    R's premises hold along the gathering from the state behind the draw: then the member's decision
    accepts, to a state of shape u.

Limits. R STANDS UNDER "FOR EVERY": THE STATEMENT IS A BRIDGE, NOT A SEAT THAT IS PAID: IT COUNTS
FOR NOTHING UNTIL A RunsLaw IS NAMED AT EACH LINK, with every runG and every pre a term (see
ClaimShape.lean's limits: a RunLaw can be idle in two ways). One way: from the shapes to the
decision. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash OnBytes.secondHashFunction. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchMember
import Johnson.Desc.First.Batch.Shape.RunGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName Claim claimsInBy claimsInStep named)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh)
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where atS drawAlone adds batch eachAtS
  ledgerEmpty addList)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)

/-! ## 1 Where the orders' runs stand -/

theorem order_places (sub : ModelPart) (first : Bool) :
    ∀ o ∈ VerifiableInference.Desc.First.orderOf sub,
    ∃ k, (kindsBeforeBatching sub first)[o.1]? = some k ∧ k ≠ KindName.K9 ∧ k ≠ KindName.K10 ∧
      2 ≤ o.1 + 1 ∧ o.1 + 1 ≤ 9 := by
  intro o ho
  cases sub <;> cases first <;>
    simp only [VerifiableInference.Desc.First.orderOf,
      VerifiableInference.Desc.First.orderCuts, List.flatten_cons,
      List.flatten_nil, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at ho <;>
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, by decide, by decide, by decide, by decide⟩

/-! ## 2 The reply is kept -/

/-- The two states hold the same reply. -/
def Kept (a b : S) : Prop := a.out.reply = b.out.reply

theorem fold_keeps (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) :
    ∀ (os : List (Nat × String)),
      (∀ o ∈ os, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
        ∀ n a cs a', run n a = .ok (cs, a') → Kept a a') →
      ∀ (x y : List Claim × S), foldE (claimsInStep each bs) os (.ok x) = .ok y → Kept x.2 y.2
  | [], _, x, y, h => by
    obtain rfl : x = y := Except.ok.inj h
    rfl
  | o :: os, hk, x, y, h => by
    rw [fold_cons] at h
    cases hs : claimsInStep each bs x o with
    | error e => rw [hs] at h; exact nomatch h
    | ok z =>
      rw [hs] at h
      have h2 := fold_keeps each bs os (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) z y h
      have h1 : Kept x.2 z.2 := by
        unfold claimsInStep at hs
        cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
        | none => rw [hl] at hs; exact nomatch hs
        | some run =>
          rw [hl] at hs
          have hn : named (o.2 ++ ": no such run") (some run) = .ok run := rfl
          rw [hn] at hs
          dsimp only [Except.bind] at hs
          cases hr : run x.1.length x.2 with
          | error e => rw [hr] at hs; exact nomatch hs
          | ok v =>
            rw [hr] at hs
            dsimp only at hs
            cases he : each o v.1 v.2 with
            | error e => rw [he] at hs; exact nomatch hs
            | ok _ =>
              rw [he] at hs
              obtain rfl := Except.ok.inj hs
              exact hk o (by simp) run hl x.1.length x.2 v.1 v.2 hr
      exact h1.trans h2

theorem set_out (s : S) (P : VerifiableInference.Desc.K9.Part) : (atS.set s P).out = s.out := by
  show ((s.putLink P.L).putFork P.F).out = s.out
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;> simp_all [S.putLink, S.putFork]

/-- The bare batching keeps the reply, where every run of the order does. -/
theorem batch_keeps (p : Where) (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n a cs a', run n a = .ok (cs, a') → Kept a a')
    (s t : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batch atS p (claimsInBy each bs order)).decide s [r] gs = .ok t) : Kept s t := by
  have h' : ((drawAlone (Cl := Claim) atS p).decide s [r] gs >>= fun t₁ =>
    (adds (Cl := Claim) atS p p.piece "the segment's" (claimsInBy each bs order)).decide t₁ [] [])
      = .ok t := h
  obtain ⟨s₁, h1, h2⟩ := (ans_bind _ _ _).1 h'
  obtain ⟨P, chi, o, -, -, -, rfl⟩ := (drawAlone_iff p s s₁ r gs).1 h1
  have h2' : (atS.part (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) >>= fun s₀ =>
    VerifiableInference.Desc.need "K9.draw-has-run" s₀.L.handed >>= fun _ =>
      claimsInBy each bs order (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) >>=
        fun x => atS.part x.2 >>= fun q => addList q.F x.1 >>= fun F =>
          (pure (atS.set x.2 { q with F := F }) : Except String S)) = .ok t := h2
  simp only [ans_bind] at h2'
  obtain ⟨-, -, -, -, x, hx, q, -, F, -, e⟩ := h2'
  obtain rfl := Except.ok.inj e
  have k1 : Kept (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) x.2 :=
    fold_keeps each bs order hk ([], _) x hx
  unfold Kept at k1 ⊢
  rw [set_out] at k1 ⊢
  exact k1

/-! ## 3 The seat -/

/-- batchG, and no mark of failure on the shape behind. -/
def batchGS (rows : Nat) (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (order : List (Nat × String)) (a : ChainSh) : Except String ChainSh :=
  (batchG rows k g order a).bind fun u => if u.marked then .error "marked" else .ok u

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At the seat a run that the order names returns only where the reply stayed. -/
theorem run_guarded (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (Lk : Link S ProofFile.Cl) (eL : cF.links[l]? = some Lk) :
    ∀ o ∈ VerifiableInference.Desc.First.orderOf (subAt l), ∀ run,
      ((Lk.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n a cs a', run n a = .ok (cs, a') → Kept a a' := by
  intro o ho run hlook n a cs a' hr
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k, hk, h9, h10, hi⟩ := order_places (subAt l) (l == 0) o ho
  obtain ⟨Lk', b, e1, e2, sp, -, Lt, -, b', -, -, -, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain l (subAt l)
      (IM.subs_scope h.scope h.reads O l hl) o.1 k hk h9 h10 hi
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans eL)
  rw [e2] at hlook
  have hb : b.claims.lookup o.2 = some run := hlook
  have hla' : b = IM.seatedAs ProofFile.sameReply b' sp.name
    { chain := 1, link := some l, piece := o.1 + 1, kind := k } := hla
  rw [hla'] at hb
  unfold IM.seatedAs at hb
  rw [lookup_guarded] at hb
  obtain ⟨run₀, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hs := guarded_same ProofFile.sameReply run₀ n a a' cs hr
  exact eq_of_beq hs

/-- **THE BRIDGE AT THE SEAT.** -/
theorem batch_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere) (b : Block S ProofFile.Cl),
      cF.links[l]? = some Lk ∧ IM.k9At Zp l = some p ∧ testsWhere Zp.p.X l 0 = some w ∧
      cF.blocksInOrder[14 * l + Lk.hear.length + 2]? = some b ∧
      Lk.order = VerifiableInference.Desc.First.orderOf (subAt l) ∧
      ∀ (R : RunsLaw Lk.hear Lk.order) (s : S) (rd : Fmt.RoundView)
        (gs : List (List (Nat × List UInt64))) (u : ChainSh),
        batchGS p.rows w.1 (fun o => (R.law o).runG) Lk.order (chainSh s) = .ok u →
        (∃ y, rd.drawn.elems = [y]) →
        (∀ F, s.fork? = some F → ledgerEmpty F = true) →
        (∀ s₁, (drawAlone (Cl := Claim) atS p).decide s [rd] gs = .ok s₁ →
          PreAll R Lk.order 0 s₁) →
        ∃ t, b.decide s [rd] gs = .ok t ∧ u = chainSh t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, w, T, eL, hp, -, -, -, -, hla, hflat, -, -, -, hord, -, -, hw, -, heach, -, -⟩ :=
    (IM.k9_of h.scope h.reads O).2 l hl
  refine ⟨Lk, p, w, _, eL, hp, hw, hflat, hord, fun R s rd gs u hg ⟨y, hy⟩ hv hpre => ?_⟩
  have hg' : (batchG p.rows w.1 (fun o => (R.law o).runG) Lk.order (chainSh s)).bind
    (fun u => if u.marked then (.error "marked" : Except String ChainSh) else .ok u) = .ok u := hg
  cases hB : batchG p.rows w.1 (fun o => (R.law o).runG) Lk.order (chainSh s) with
  | error e => rw [hB] at hg'; exact nomatch hg'
  | ok u₁ =>
    rw [hB] at hg'
    have hg'' : (if u₁.marked then (.error "marked" : Except String ChainSh) else .ok u₁) =
      .ok u := hg'
    by_cases hm : u₁.marked = true
    · rw [if_pos hm] at hg''
      exact nomatch hg''
    · rw [if_neg hm] at hg''
      obtain rfl := Except.ok.inj hg''
      obtain ⟨t, ht, rfl⟩ := batch_follows w.1 R p s rd gs u₁ hB y hy hv hpre
      refine ⟨t, ?_, rfl⟩
      rw [heach]
      refine (IM.yes_alone (hla _) (by intro k; cases k) s t [rd] gs).2 ⟨ht, ?_, ?_⟩
      · have : t.failed.isSome = false := by
          have e : (chainSh t).marked = t.failed.isSome := rfl
          rw [← e]
          simpa using hm
        simpa using this
      · have hk := batch_keeps p (eachAtS w.1) Lk.hear Lk.order
          (by rw [hord]; exact run_guarded h l hl Lk eL) s t rd gs ht
        unfold ProofFile.sameReply
        rw [hk]
        exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.batch_keeps
#print axioms Johnson.AtFull.Shape.run_guarded
#print axioms Johnson.AtFull.Shape.batch_named
#print axioms Johnson.AtFull.Shape.order_places
#print axioms Johnson.AtFull.Shape.fold_keeps
#print axioms Johnson.AtFull.Shape.set_out
#print axioms Johnson.AtFull.Shape.Kept
#print axioms Johnson.AtFull.Shape.batchGS
