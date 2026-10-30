-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3Join.lean: THE NINTH OF THE NINE ENTRIES OF THE LOOKUP ARGUMENT
THAT THE THREE SORTS' LISTS NAME (2 + 4 + 3): THE ATTENTION's "join": WHAT AN ATTENTION LINK STATES
AT (2, "join") IS THE LOOKUP's BARE RUN; AND SO THE SEVEN FIELDS "A YES OF THE RUN KEEPS .." OF
WHAT IS LEFT OF K9 (`LookRest`'s k3d, k3g, k3f, k3p, k3s, k3sL, SortFour.lean: LookRest is SortRest
less h4; k3k, LinkRestAtSort3C.lean) HOLD AT THAT ENTRY. (THE HEAD's ORDER HAS ONE ENTRY MORE AT
WHICH joinRun STANDS: (3, "join"): it is the output head's kind's own entry and none of the nine.)
Theorems: a tie and calls. After the pattern of SortK3Objects.lean and SortK3Planes.lean, which
have the other eight entries.

By. The tie: K5's files' own K05_join_of_open (Johnson/H2K5R/JoinAtOpen.lean: what
"find?" finds under "join" in what the seated link's block 2 states is K3.joinRun (K3.seatCalls
K3Lot.ofForm) (keysOfO a)), with find_of_lookup (HitemsStill.lean). The seven: the lookups' own
theorems on the bare run: join_puts, join_core (Top/H/Keep/RunsPutFork.lean) · join_more with
keepsDoor_of_more, good9_of_more, numOf_of_more (PutsMore.lean) · join_kap with kapOf_of_puts
(PutsKap.lean).

What is said. `at_join_is`: **run = K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a)**, from an
opening O, Bs.G₀.W.p4 = true, g < Bs.G₀.W.NGr, Bs.G₀.W.A[g]? = some a, c.links[2 * g + 1]? = some L
and At L (2, "join") run · `k3p_join`, `k3s_join`, `k3sL_join`, `k3d_join`, `k3g_join`, `k3f_join`,
`k3k_join`: the fields' own texts at that entry.

NOT HERE: field k3 (RunOk) at "join": it wants the caller's clause hkv.

Limits. On texts alone: no state is shown to be reached. Every hash setting (the opening's letter o
is free). Nothing on soundness.

-/
import Johnson.H2K5R.JoinAtOpen
import Johnson.Top.H.Keep.PutsMore
import Johnson.Top.H.Keep.PutsKap
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.KapRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (keysOfO K05_join_of_open)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.OnPublicFiles (k03_atS2_calls join_puts join_core join_more join_kap
        keepsDoor_of_more good9_of_more numOf_of_more kapOf_of_puts)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
  (h4 : Bs.G₀.W.p4 = true) {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan}
  (ha : Bs.G₀.W.A[g]? = some a) {L : Link S Claim} (hL : c.links[2 * g + 1]? = some L)
include O h4 hg ha hL

/-- **WHAT AN ATTENTION LINK STATES UNDER "join" IS THE LOOKUP's OWN RUN.** -/
theorem at_join_is {run : ℕ → S → Except String (List Claim × S)}
    (h : At L (2, "join") run) :
    run = K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a) := by
  obtain ⟨Lk, h1, h2⟩ := K05_join_of_open O h4 hg ha
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans hL)
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.1 h
  have hb' : Lk.hear[2]? = some b := hb
  have hl' : b.claims.lookup "join" = some run := hl
  obtain ⟨x, hx, hx2⟩ := find_of_lookup "join" b.claims run hl'
  have e : K9.statesOfLink Lk 2 = b.claims := by
    unfold K9.statesOfLink
    rw [hb']
    rfl
  rw [e, hx] at h2
  rw [← hx2]
  exact congrArg Prod.snd (Option.some.inj h2)

/-- **k3p at "join".** -/
theorem k3p_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → ∃ G, e₁ = e.putFork G := by
  rw [at_join_is O h4 hg ha hL h]
  exact join_puts _ k03_atS2_calls _

/-- **k3s at "join".** -/
theorem k3s_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork Sized e → HasFork Sized e₁ := by
  rw [at_join_is O h4 hg ha hL h]
  rintro n e cl e₁ hq ⟨G₀, hF, hz⟩
  obtain ⟨G, rfl, _, _, hG⟩ := join_core _ k03_atS2_calls _ n e cl e₁ G₀ hF hz hq
  exact ⟨G, fork_putFork e G₀ hF G, hG⟩

/-- **k3sL at "join".** -/
theorem k3sL_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁ := by
  rw [at_join_is O h4 hg ha hL h]
  rintro n e cl e₁ hq ⟨G₀, hF, hz, hn⟩
  obtain ⟨G, rfl, e1, e2, hG⟩ := join_core _ k03_atS2_calls _ n e cl e₁ G₀ hF hz hq
  exact ⟨G, fork_putFork e G₀ hF G, hG, by rw [e1, e2]; exact hn⟩

/-- **k3d at "join".** -/
theorem k3d_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → KeepsDoor atS e e₁ := by
  rw [at_join_is O h4 hg ha hL h]
  exact keepsDoor_of_more (join_more _ k03_atS2_calls _)

/-- **k3g at "join".** -/
theorem k3g_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → good9 e → good9 e₁ := by
  rw [at_join_is O h4 hg ha hL h]
  exact good9_of_more (join_more _ k03_atS2_calls _)

/-- **k3f at "join".** -/
theorem k3f_join (u : HTailF2) (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join")
  run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → numOf u e₁ = numOf u e := by
  rw [at_join_is O h4 hg ha hL h]
  exact numOf_of_more (join_more _ k03_atS2_calls _) u

/-- **k3k at "join".** -/
theorem k3k_join (run : ℕ → S → Except String (List Claim × S)) (h : At L (2, "join") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → kapOf e₁ = kapOf e := by
  rw [at_join_is O h4 hg ha hL h]
  exact kapOf_of_puts (join_kap _ k03_atS2_calls _)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.at_join_is
#print axioms VerifiableInference.Desc.LinkJoin.k3p_join
#print axioms VerifiableInference.Desc.LinkJoin.k3s_join
#print axioms VerifiableInference.Desc.LinkJoin.k3sL_join
#print axioms VerifiableInference.Desc.LinkJoin.k3d_join
#print axioms VerifiableInference.Desc.LinkJoin.k3g_join
#print axioms VerifiableInference.Desc.LinkJoin.k3f_join
#print axioms VerifiableInference.Desc.LinkJoin.k3k_join
