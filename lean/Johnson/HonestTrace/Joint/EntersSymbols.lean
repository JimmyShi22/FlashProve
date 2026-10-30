-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbols.lean

Nothing on hiding. No property of the protocol is claimed. Two definitions of premises' forms and
two theorems, at letters: the Script Q, the coins k, the input v, the trace τ and the predicate P are letters.

"ScriptSymsRawOn" (Johnson/Goal/HonestTrace/ConstrAtThread.lean) asks its equation at EVERY list of challenges, the empty one too.
The laws on a Script's text speak at lists no shorter than a bound. The two meet where the entries at the layout's seats read no
challenge.

Main definitions and theorems:
* "SeatEntriesReadNoChallenge Zp Q k v P": at each seat (message, row, place) of the layout, inside the sizes, on the entries that
  P picks: the message's entry in the main row is the same at any two lists of challenges.
* "SeatEntriesArePackedAt Zp Q k v τ P heard": the plain equation at ONE list "heard": that entry is the library's packing of τ.
* "rawOn_of_one_list": the two give ScriptSymsRawOn on P.
* "rawOn_of_long_lists": the same from the equation in ScriptSymsRawOn's own form at every list no shorter than a bound N, and one
  such list.

Limits. Neither premise is shown of any Script. "SeatsFixed" is not asked.
"SeatEntriesReadNoChallenge" speaks at bare lists of challenges; the senders' sentence speaks at
lists cut at the message's own bound: so it asks more than that sentence gives. Where the senders'
sentence stands at the bound 0 it is not needed (EntersSymbolsAtEveryList.lean).
-/
import Johnson.Goal.HonestTrace.ConstrAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open VerifiableInference.Desc.Sound (MsgT)
open Meaning (msgOf)
open P5J (CellsM)
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {Bk : ProverCoinCounts} {W₀ Rc T : Type}

/-- **The entries at the layout's seats read no challenge**, at one run's coins k and one input v, on the entries that P picks. -/
def SeatEntriesReadNoChallenge (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (P : ℕ → ℕ → Prop) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ m < 25, ∀ a < (s m).NM, P m a → ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
    ∀ heard heard' : List Fmt.Drawn,
      Q.msg (f (Meaning.labAt X m a) i' c).1 k v heard false
          (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2 =
        Q.msg (f (Meaning.labAt X m a) i' c).1 k v heard' false
          (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2

/-- **The plain equation at one list of challenges**: the entries at the layout's seats are the library's packing of τ. -/
def SeatEntriesArePackedAt (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (τ : Tr) (P : ℕ → ℕ → Prop)
    (heard : List Fmt.Drawn) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ m < 25, ∀ a < (s m).NM, P m a → ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
    Q.msg (f (Meaning.labAt X m a) i' c).1 k v
        (heard.take (Q.fixedMsg (f (Meaning.labAt X m a) i' c).1)) false
        (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2 =
      msgOf s τ (Meaning.labAt X m a) false i' c

variable {Zp : ProofFile.Pub}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {τ : Tr} {P : ℕ → ℕ → Prop}

/-- **From one list to every list.** -/
theorem rawOn_of_one_list (noChallenge : SeatEntriesReadNoChallenge Zp Q k v P)
    {heard : List Fmt.Drawn} (packed : SeatEntriesArePackedAt Zp Q k v τ P heard) :
    ScriptSymsRawOn Zp Q k v τ P :=
  fun _ m hm a ha hP i' hi' c hc =>
    (noChallenge m hm a ha hP i' hi' c hc _ _).trans (packed m hm a ha hP i' hi' c hc)

/-- **From the long lists to every list**: N is any bound; "heard" is one list that reaches it. -/
theorem rawOn_of_long_lists (noChallenge : SeatEntriesReadNoChallenge Zp Q k v P) {N : ℕ}
    (packed : ∀ heard : List Fmt.Drawn, N ≤ heard.length → SeatEntriesArePackedAt Zp Q k v τ P heard)
    {heard : List Fmt.Drawn} (long : N ≤ heard.length) : ScriptSymsRawOn Zp Q k v τ P :=
  rawOn_of_one_list noChallenge (packed heard long)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.rawOn_of_one_list
#print axioms OnBytes.HonestTrace.rawOn_of_long_lists
