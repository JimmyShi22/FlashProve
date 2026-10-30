-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Rows.lean: CONDITIONAL: what the row that a masked sumcheck of
an attention segment leaves is worth, where the rounds heard are the honest part's. Statements with
their proofs, and one definition. The reading is the library's own (`Reading.gl`).

The verifier hears a sumcheck (`hear`, Johnson/Desc/Part/MaskedSum4.lean) and later makes its row: a
form (`formOf`, Johnson/Desc/First/Att/LeftP.lean) with an end term S0 made of what the ledger shows
for the end values. The law of the honest part says what that form is worth in any world
(`rowForm_worth`, Honest/SumLaw/More.lean), given `SumsTo`; Honest/K5/Law/SumsTo.lean pays `SumsTo`
for a tame summand.

EVERY STATEMENT ON A ROW IS CONDITIONAL. The premises, and who is meant to pay each:
  the summand is tame (`Summand.Tame`)                       whoever lays the summand
  the rounds heard are the part's, played alone at coins c   whoever shows what the row plays
  the world has the hiding polynomial's coins under the sumcheck's own slots
                                                             whoever ties the mask row to the coins
  the claimed form is worth the summand's total              whoever states the sumcheck's start
  the end term reads as the formula on the end values sent   for the seven sumchecks of products:
                                                             `s0_is_cf` with `shown_reads`
`s0_is_cf` stands in Johnson/Desc/K5/Honest/Law/Sc3.lean.
NONE OF THESE IS SHOWN HERE OF A SUMMAND OF THE PROTOCOL.
Main names:
  `shownVal`         end value number n as it is sent, read
  `formOf_rowForm`   the kind's copy of the row's form is the part's
  `heard_r_length`   a hearing of the part's rounds has a challenge for each variable
  `row_worth`        the row's worth: eps (S0 + kept - the formula on the end values sent)
  `row_zero`         **the row is worth 0**: one statement for all eight sumchecks
  `shown_is_sent`, `shown_reads`   what a later ledger shows under the end values' slots
  `row_zero_products`, `row_zero_left`   the row that `left` makes of a sumcheck of products is
                     worth 0; in the second, what the ledger shows is paid by `shown_reads`
  `take_is_chal`     the verifier's cut of a sumcheck's challenges is the point of the summand

Limits. One sumcheck, played alone; that the frame's play yields these rounds is another file's.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SumsTo
import Johnson.Desc.K5.Honest.Law.Sc3
import Johnson.Desc.First.Att.K5LeftLaw
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call Heard hear ownSlots rowForm)
open VerifiableInference.Desc.First.Att.P (formOf left chal)
open VerifiableInference.Desc.Part.MaskedSum (ledger_shown)
open VerifiableInference.Desc.First.Att.P (left_spec shown_val)
open ProofFile.Honest.SumLaw
open H2K5.Honest (Summand pairsOf s0_is_cf)

variable {V W X : Type}

/-- End value number n as it is sent, read: the map that goes under the mask entry, at the
variables' challenges, plus Y's challenge times the mask entry. L: the challenges, Y's last. m: the
mask entries. -/
def shownVal {K : Type} [Field K] (ρ : Reading K) (S : Summand) (L m : List E) (n : Nat) : K :=
  ρ.val (S.endAt (L.take S.vars) n) + ρ.val (L.getD S.vars zeroE) * ρ.val (m.getD n zeroE)

/-- The kind's copy of the row's form is the part's. -/
theorem formOf_rowForm (h : Heard) (S0 : E) (kept : Aff) : formOf h S0 kept = rowForm h S0 kept :=
  rfl

/-- A hearing of the part's rounds has a challenge for each variable, Y among them. -/
theorem heard_r_length (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff)
    (F G : Fork) (h : Heard) (hd : drawsOk (J.callAt t.input (frontOf t seen)) dr = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen dr = some rounds)
    (hh : hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G)) :
    h.r.length = (J.callAt t.input (frontOf t seen)).all.length := by
  obtain ⟨d0, dv, dl, T, _, hv, _, _, rfl⟩ := heard_spec hd ha hh
  show (dv.map elemOf).length = _
  rw [List.length_map, hv]

/-- The same at a job made of a summand: one challenge more than the summand has variables. -/
theorem heard_r_vars (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard)
    (hvs : k.vs = ds.map Var.plain) (he : k.ends = some e)
    (hv : ds.length = (S t.input (frontOf t seen)).vars) (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G)) :
    h.r.length = (S t.input (frontOf t seen)).vars + 1 := by
  have ec := callAt_jobOf k lead S t.input (frontOf t seen)
  have := heard_r_length (V := V) name endName (jobOf k lead S) c t seen dr rounds C F G h
    (by rw [ec]; exact hd) ha (by rw [ec]; exact hh)
  rw [ec] at this
  rw [this]
  unfold Call.all
  rw [he, hvs, List.length_append, List.length_map, List.length_singleton, hv]

/-- **The verifier's cut of the challenges is the honest side's**: the verifier's weights read
`chal h`, all challenges but the last, as an array; the summand is evaluated at the first `vars` of
them. -/
theorem take_is_chal (h : Heard) (n : Nat) (hl : h.r.length = n + 1) :
    (h.r.take n).toArray = chal h := by
  unfold chal
  rw [List.dropLast_eq_take, hl, Nat.add_sub_cancel]

/-- **What the row that a sumcheck leaves is worth**, in any world, CONDITIONAL on: the summand is
tame; the rounds heard are the honest part's, played alone at the coins c; the world has the hiding
polynomial's coins under the sumcheck's own slots; the claimed form is worth the summand's total. -/
theorem row_worth (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (S0 : E)
    (kept : Aff) (Wd : World GE) (hvs : k.vs = ds.map Var.plain) (he : k.ends = some e)
    (hT : (S t.input (frontOf t seen)).Tame Reading.gl ds e.dY) (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total) :
    (formOf h S0 kept).value Reading.gl Wd = Reading.gl.val h.eps *
      (Reading.gl.val S0 + kept.value Reading.gl Wd -
        (S t.input (frontOf t seen)).formula Reading.gl
          (h.r.take (S t.input (frontOf t seen)).vars)
          (shownVal Reading.gl (S t.input (frontOf t seen)) h.r (endRun c))) := by
  have ec := callAt_jobOf k lead S t.input (frontOf t seen)
  have hlen := heard_r_vars (V := V) name endName k ds e lead S c t seen dr rounds C F G h hvs he
    hT.vars hd ha hh
  have hS := sumsTo_of_tame_at Reading.gl k ds e lead S t.input (frontOf t seen) hvs he hT
    (endRun c) h.r hlen
  rw [← hσ] at hS
  rw [formOf_rowForm, rowForm_worth (V := V) name endName (jobOf k lead S) c t seen dr rounds C F G
    h S0 kept Wd _ (by rw [ec]; exact hd) ha (by rw [ec]; exact hh) (by rw [ec]; exact hm)
    (by rw [ec]; exact hS), last_is_formula_at Reading.gl _ ds e.dY hT (endRun c) h.r hlen]
  rfl

/-- **The row is worth 0**, CONDITIONAL as `row_worth`, and on: the end term S0 reads as the
summand's formula on the end values as they are sent. One statement for all eight sumchecks. -/
theorem row_zero (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (S0 : E)
    (Wd : World GE) (hvs : k.vs = ds.map Var.plain) (he : k.ends = some e)
    (hT : (S t.input (frontOf t seen)).Tame Reading.gl ds e.dY) (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total)
    (hS0 : Reading.gl.val S0 = (S t.input (frontOf t seen)).formula Reading.gl
      (h.r.take (S t.input (frontOf t seen)).vars)
      (shownVal Reading.gl (S t.input (frontOf t seen)) h.r (endRun c))) :
    (formOf h S0 {}).value Reading.gl Wd = 0 := by
  rw [row_worth (V := V) name endName k ds e lead S c t seen dr rounds C F G h S0 {} Wd hvs he hT
    hd ha hh hm hσ, Aff.value_empty, hS0]
  ring

/-- What a later ledger shows under the end values' slots reads as the job's end values, each plus
Y's challenge times its coin: at every job. CONDITIONAL on: the ledger in front is sized; the rounds
heard are the honest part's. -/
theorem shown_is_sent (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff)
    (F G H : Fork) (h : Heard) (e : Ends) (he : J.shape.ends = some e)
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) dr = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen dr = some rounds)
    (hh : hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hF : OnBytes.PscRun.Sized F) (hl : OnBytes.PscRun.Later G H) :
    ∀ j, j < e.n → Reading.gl.val (H.vp.getD (h.sEnd + j) zeroE) =
      Reading.gl.val ((J.ends t.input (frontOf t seen) (h.r.take J.shape.vs.length)).getD j zeroE) +
        Reading.gl.val (h.r.getLastD zeroE) * Reading.gl.val ((endRun c).getD j zeroE) := by
  intro j hj
  have hk : J.callAt t.input (frontOf t seen) =
      ⟨J.shape.lead, withPoints J.shape.vs (J.points t.input (frontOf t seen)), some e⟩ := by
    show (⟨J.shape.lead, _, J.shape.ends⟩ : Call) = _
    rw [he]
  obtain ⟨d0, dv, dl, T, hds, hv, hs, hR, hh'⟩ := heard_spec hd ha hh
  have hpos : 0 < dv.length := by rw [hv]; exact all_pos J _ _ e he
  have hrr : h.r = dv.map elemOf := by rw [hh']
  have hh2 := hh
  have hR2 := hR
  rw [hk] at hh2 hR2
  have key := shown_val (ledger_shown hF hh2 hR2 hl j hj)
  have hvals : (readOf J c t seen d0 dv).values =
      (saidEnds J e (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c) (endRun c)
        (drawnE (d0 :: dv)) t.input).map canon := by
    simp only [readOf, he]
  obtain ⟨e1, e2⟩ := drawn_vars (J.callAt t.input (frontOf t seen)) d0 dv dl hv hpos
    J.shape.vs.length
  rw [← key, hvals, ends_reads J e _ _ _ _ _ _ j hj, e1, e2, varsOf_cons _ d0 dv dl hv, hrr]

/-- **What a later ledger shows under the end values' slots reads as the end values as they are
sent**, CONDITIONAL on: the ledger in front is sized; the rounds heard are the honest part's; the
summand has as many end values as the call. -/
theorem shown_reads (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G H : Fork) (h : Heard)
    (hvs : k.vs = ds.map Var.plain) (he : k.ends = some e)
    (hv : ds.length = (S t.input (frontOf t seen)).vars)
    (hn : (S t.input (frontOf t seen)).ends = e.n) (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G)) (hF : OnBytes.PscRun.Sized F)
    (hl : OnBytes.PscRun.Later G H) :
    ∀ j, j < e.n → Reading.gl.val (H.vp.getD (h.sEnd + j) zeroE) =
      shownVal Reading.gl (S t.input (frontOf t seen)) h.r (endRun c) j := by
  intro j hj
  have ec := callAt_jobOf k lead S t.input (frontOf t seen)
  have hlen := heard_r_vars (V := V) name endName k ds e lead S c t seen dr rounds C F G h hvs he
    hv hd ha hh
  rw [shown_is_sent (V := V) name endName (jobOf k lead S) c t seen dr rounds C F G H h e he
    (by rw [ec]; exact hd) ha (by rw [ec]; exact hh) hF hl j hj]
  show Reading.gl.val (((S t.input (frontOf t seen)).endsAt (h.r.take k.vs.length)).getD j zeroE) +
    _ = _
  have hlast : h.r.getLastD zeroE = h.r.getD (S t.input (frontOf t seen)).vars zeroE := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD]
  rw [Summand.endsAt_getD _ _ j (by rw [hn]; exact hj), hvs, List.length_map, hv, hlast]
  rfl

/-- **The row that the verifier makes of a sumcheck of products is worth 0**, CONDITIONAL as
`row_worth`, and on: the summand's terms at the challenges are weighted products; the verifier's
weights are as many and read alike; what the ledger H shows under the end values' slots reads as the
end values as they are sent. The premise on the weights is paid by whoever reads the weights: with
`take_is_chal` both sides stand at the same challenges of this sumcheck, and what is left is that
the other challenges which a weight reads are the verifier's. -/
theorem row_zero_products (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G H : Fork) (h : Heard)
    (Wd : World GE) (np : Nat) (Wo Wt : Array E) (f : Aff) (hvs : k.vs = ds.map Var.plain)
    (he : k.ends = some e) (hT : (S t.input (frontOf t seen)).Tame Reading.gl ds e.dY)
    (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total)
    (hf : left H h Wt = some f)
    (ht : (S t.input (frontOf t seen)).terms (h.r.take (S t.input (frontOf t seen)).vars) =
      pairsOf np Wo)
    (hsz : Wt.size = np)
    (hW : ∀ b, b < np → Reading.gl.val (Wt.getD b zeroE) = Reading.gl.val (Wo.getD b zeroE))
    (hsh : ∀ j, j < 2 * np → Reading.gl.val (H.vp.getD (h.sEnd + j) zeroE) =
      shownVal Reading.gl (S t.input (frontOf t seen)) h.r (endRun c) j) :
    f.value Reading.gl Wd = 0 := by
  rw [left_spec hf]
  exact row_zero (V := V) name endName k ds e lead S c t seen dr rounds C F G h _ Wd hvs he hT hd ha
    hh hm hσ (s0_is_cf Reading.gl _ _ np Wo Wt _ _ ht hsz hW hsh)

/-- **The same, with what the ledger shows paid**: CONDITIONAL as `row_zero_products` but for its
last premise, and on: the summand and the call have 2 np end values; the ledger in front of the
hearing is sized; H, the ledger at which the verifier makes the row, is later than the one that the
hearing hands back. Whoever follows the ledger along the rest of the kind's hearing pays the last
two. -/
theorem row_zero_left (name endName : String) (k : Call) (ds : List Nat) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G H : Fork) (h : Heard)
    (Wd : World GE) (np : Nat) (Wo Wt : Array E) (f : Aff) (hvs : k.vs = ds.map Var.plain)
    (he : k.ends = some e) (hT : (S t.input (frontOf t seen)).Tame Reading.gl ds e.dY)
    (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total)
    (hf : left H h Wt = some f)
    (ht : (S t.input (frontOf t seen)).terms (h.r.take (S t.input (frontOf t seen)).vars) =
      pairsOf np Wo)
    (hsz : Wt.size = np)
    (hW : ∀ b, b < np → Reading.gl.val (Wt.getD b zeroE) = Reading.gl.val (Wo.getD b zeroE))
    (hn : (S t.input (frontOf t seen)).ends = e.n) (hen : e.n = 2 * np)
    (hF : OnBytes.PscRun.Sized F) (hl : OnBytes.PscRun.Later G H) :
    f.value Reading.gl Wd = 0 :=
  row_zero_products (V := V) name endName k ds e lead S c t seen dr rounds C F G H h Wd np Wo Wt f
    hvs he hT hd ha hh hm hσ hf ht hsz hW fun j hj =>
      shown_reads (V := V) name endName k ds e lead S c t seen dr rounds C F G H h hvs he hT.vars hn
        hd ha hh hF hl j (by rw [hen]; exact hj)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.formOf_rowForm
#print axioms ProofFile.Honest.K5.heard_r_length
#print axioms ProofFile.Honest.K5.heard_r_vars
#print axioms ProofFile.Honest.K5.take_is_chal
#print axioms ProofFile.Honest.K5.row_worth
#print axioms ProofFile.Honest.K5.row_zero
#print axioms ProofFile.Honest.K5.shown_is_sent
#print axioms ProofFile.Honest.K5.shown_reads
#print axioms ProofFile.Honest.K5.row_zero_products
#print axioms ProofFile.Honest.K5.row_zero_left
