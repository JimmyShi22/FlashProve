# A full-size proof under a clipped-gap policy

One proof at the size of Llama 4 Maverick, on synthetic weights, under an acceptance policy that tolerates tokens other than the model's first choice, with the public files that the verifier needs to check it. The programs make these weights up themselves; no weight file of Meta's was used. A few constants in `config/` go back to work on real models: see [How the files were made](#how-the-files-were-made). No GPU is needed. Read [../accepted-proof-clipped-gap/](../accepted-proof-clipped-gap/README.md) first, for the policy, and [../full-size/](../full-size/README.md), for the size: the files are named as there.

## Try it

From the repository's top directory, after `verifier/build.sh`. As in the other examples, the commitment ID after `-id` and the values after `-policy` come with the example; in a real check they must not. The call below, without `-j` (one thread for its longest stage), took about 21 seconds in one call (not on the released programs; like calls on [the full-size example](../full-size/README.md#try-it) took up to 66.2 seconds), on the machine that had just made these files (24 CPUs of a shared machine; the files were still in its file cache), and its largest process held about 3.5 GB of memory at its peak. Expect longer on a slower or busier machine.

```sh
bin/cp_verify examples/full-size-clipped-gap/config examples/full-size-clipped-gap/ivk \
  examples/full-size-clipped-gap/example.req examples/full-size-clipped-gap/example.y \
  examples/full-size-clipped-gap/example.proof \
  -id d62a9c1f6542db1e8ca422d0f50b2b9b40bf505c6bbfa87ec003bcae69c49191 \
  -policy clipped-gap,25856,512,1,15,8 -q
```

The call ends with exit code 0. Its last four lines:

```
commitment: 86 closeness rounds of the one-time files rest on another source than the bound within a third of the distance; the table has a record: the binding of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given
proof of work: up to 32 bits counted in 71 rounds; with it the least round has 128.00 bits, without it 96.23 bits
result-v1 status=0 claim=policy id=d62a9c1f6542db1e8ca422d0f50b2b9b40bf505c6bbfa87ec003bcae69c49191 bits=128 work=32 work-rounds=71 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=86 record=1 r=23 e=1024 T=1024 tokens=24..1023 y=yes policy=clipped-gap C=25856 theta=512 cap=1 s=15 sh=8 sT=4 F=24 above-clip=1 leaf=0 stages=key,leaf,request dw=8 build=<64 hex digits>
WITHIN LIMITS: clipped-gap C=25856 theta=512 cap=1 s=15 sh=8
```

The last line is the answer. `WITHIN LIMITS` is not `YES`, although the exit code is the same. The other three lines read as in [the full-size example](../full-size/README.md#try-it), whose page explains them; the bits that they print are the C++ programs' own accounting, not a theorem.

## The policy

The commitment ID covers `policy.txt`, so this policy has a commitment of its own, apart from [../full-size/](../full-size/README.md)'s.

The logit gap of a checked token is the largest logit at its position minus the token's own logit, plus 1 if a token with the largest logit has a lower token ID. It is 0 for the model's first choice. A token's cost is its logit gap plus 2^sh, here 256. Three lines of `policy.txt` limit the costs of the checked tokens:

| line | meaning |
|---|---|
| `C 25856` | the clip: a cost above C counts as C |
| `theta 512` | counted in this way, the costs average at most theta |
| `cap 1` | at most this many tokens cost more than C |

The exact match is the case C = theta = 2^sh and cap = 0: no token may cost more than a first choice does.

The three limits were not fitted to any model or reply. They were chosen so that what passes follows from the policy's definition: with m = 2^sh = 256, the cost of a first choice, theta is 2 m, C is 101 m and cap is 1. Under them one token of any cost passes once 100 tokens are covered, if all the others are the model's first choices. They show how the policy works and are no pattern for a provider, who fits limits of its own on its own engine's replies. The script with which a provider can fit them is [fit_limits.py](../../integrations/vllm/integer_model/examples/fit_limits.py); [the small example's configuration](../../prover/examples/target_small_f2_gap/README.md#how-the-limits-were-fitted) has limits that were fitted with it.

`-policy` states the policy that you expect: its kind, then the lines `C`, `theta`, `cap`, `s` and `sh`. If you leave the option out, or `policy.txt` sets other values, the call ends `NO: policy`, exit code 1. `s` states the unit of the logits: a logit of the model is an integer logit divided by 2^s. It is the provider's statement, and nothing in the proof ties it to the model.

## What passes under these limits, and what does not

This follows from the policy's definition and needs no run. Here "passes" means: meets the limits. Let R tokens be checked ("covered", in the words above), all of them first choices but k, and let each of the k cost more than C. Counted as at most C each, the costs sum to 256 × (R - k) + 25,856 × k. The policy asks that this sum is at most 512 × R, and that k is at most 1.

- R = 1,000, k = 1: 256 × 999 + 25,856 = 281,600, which is at most 512 × 1,000 = 512,000; and one token costs more than C. Inside the limits, whatever that token is.
- R = 99, k = 1: 256 × 98 + 25,856 = 50,944, which is more than 512 × 99 = 50,688. Outside, by the average alone. With R = 100 the two are equal, 51,200: inside, at the very limit.
- R = 1,000, k = 2: 256 × 998 + 25,856 × 2 = 307,200, which is at most 512,000, so the average is met; but two tokens cost more than C. Outside, by the count alone.

A departure that costs C or less is counted in full, and does not count against `cap`. So with R = 99, if the other 98 tokens are first choices, one such token passes if it costs at most 25,600.

## The request

`example.req` holds 1,024 tokens, then r = 23 and e = 1024. Tokens 0 to 23 are the prompt, the same 24 tokens as in [../full-size/](../full-size/README.md). Tokens 24 to 523 are tokens that the integer model chose itself, one after another, the same as in that example's request. Token 524 is the model's second choice at its place: token ID 28099, whose logit gap is 10,745,259, so that it costs 10,745,515. Tokens 525 to 1023 are the model's first choices again, given token 524 (how they were grown: [below](#how-the-files-were-made)). The other 999 checked tokens cost 256 each. So the reply leaves the model's first choices once and goes on from there, as a reply served by another engine can. No engine served this one: we put the departure in. The proof shows none of what is said here of each token's choice and cost: that rests on one run of our own of the integer model on these weights. And the token after the request, 61122 (in `example.y`), is the committed model's first choice after the last token: that the proof does state.

This example is the first bullet's case (R = 1,000, k = 1): its one departure is counted as 25,856. Beside that departure, the other tokens' costs could rise by 230,400 in all, as long as none of them comes to more than C, and the reply would still pass: for example, 900 of the other tokens, each with a logit gap of 256.

## What WITHIN LIMITS says

The proof states that the costs of tokens 24 to 1023 together meet the three limits under the committed model, and that the token after the request is the one that the committed model ranks first.

It does not say that any of these 1,000 tokens is the model's first choice. Lean's soundness theorem on `verify` is for exact match only, and is of the verifier written in Lean, not of `cp_verify`; for a policy such as the clipped gap, Lean's theorem says only that the output meets the policy, which by itself bars little ([limits](../../docs/limits.md#within-limits)).

The limits are set by whoever made the commitment. They bound costs that are measured on the committed model's logits, which no verifier sees. Where the logits lie close together, several tokens cost C or less, and any of them can stand at that place if the other tokens' costs leave room in the average: along [../full-size/](../full-size/README.md)'s request the model's second choice costs no more than C at 7 of the 1,000 checked places (one run of the integer model, not on the released programs). And under these limits one of the 1,000 tokens can be any token at all, if the others are first choices: the field `above-clip=1` of the line `result-v1` above (and of the line `covered:`, further up in the output) says so. That field is the policy's own bound, reckoned from the limits and the number of checked tokens; it does not count what happened in this reply, and it would read the same for a reply of first choices alone. Whether replies of a nearby model meet these limits was not measured ([the small example](../accepted-proof-clipped-gap/README.md#what-within-limits-says) tells what was measured there). What each answer under such a policy tells a client about the model's hidden scores, by design, is told in [docs/what-is-not-hidden.md](../../docs/what-is-not-hidden.md#served-or-failed).

The model has Maverick's shape (48 layers, 128 routed experts) and none of its weights: they come from a generator. So this answer shows how large the files of a full-size proof under such a policy are and what checking one costs on your machine. Like the other examples', it says nothing about any model that anyone serves. Your part in a real check is described in [../accepted-proof/](../accepted-proof/README.md#what-the-yes-says).

As in `../accepted-proof/`, the model is synthetic, and the ID, the request and the values after `-policy` came in the same package as the proof. In real use, get the ID before you send the prompt, from the party that vouches for the model, not through the server you are checking (best from where the commitment is published); fix the limits that you accept before the proof is made; and never take either from the files that you are checking. Acceptance policies in a real check: [docs/verifying.md](../../docs/verifying.md#acceptance-policies).

## How the files were made

At the configuration [prover/examples/target_full_f2_gap](../../prover/examples/target_full_f2_gap), on one H100, with calls like the two in [../accepted-proof/README.md](../accepted-proof/README.md#how-the-files-were-made): `cp_commit` also got `-keep-for-the-audit`, and `cp_prove` also got `-in-step 1 -memory lean`. `-memory lean` lays out the GPU's memory in another way; by the program's own help the proofs stay the same. These files were not made by the released programs, so they show nothing of the released prover. `cp_commit` drew the seed. The secret directory of this example is not part of the repository. We cannot show that no copy of it exists; the weights are synthetic, so nothing depends on it. `ivk/` holds `key.bin` and the one stored copy's file that this proof names, `leaf/0.bin`.

Before any call of `cp_prove`, the audit script that came with the programs that made the files, `tools/audit/audit_commitment.sh`, audited the commitment, and it passed; a pass covers little. It compared 10.20 % of the bytes of `ivk/key.bin` and `ivk/leaf/0.bin` by value; no false kept bytes were tried ([what a YES does not cover](../../tools/audit/README.md#what-a-yes-does-not-cover); row H13.7 of [the table of all rows](../../docs/limits-all-rows.tsv)).

`config/policy.txt` is [prover/examples/target_full_f2](../../prover/examples/target_full_f2)'s with the three lines `C`, `theta` and `cap` changed, and `config/KL.bin` and `config/layout.txt` are that configuration's, byte for byte; so what [../full-size/](../full-size/README.md#how-the-files-were-made) says of their constants holds here too.

`example.req` was grown with `IntegerModel.extend` of the integer-model package, on the same synthetic weights, on one H100: the first 524 tokens of [own_choices.req](../../prover/examples/target_full_f2/own_choices.req) in one call; then, as token 524, the token with the second largest logit at its position (in the order: the larger logit first, of equal logits the lower token ID first); then one call for each further token, each time the model's first choice: 499 tokens and `example.y`. All 499 differ from own_choices.req's at the same places. The whole request was then scored in one fresh call: no range condition failed, each grown token came out as the model's first choice again, and the costs that this page gives for this request's tokens come from that call. [Its README, "A request from the model's own reply"](../../integrations/vllm/integer_model/README.md#a-request-from-the-models-own-reply), prints the loop for first choices at small size; the script that drove it at full size is not in this repository, and no record of the run is.

The route on Llama 4 Maverick's own weights is in [../maverick/](../maverick/README.md).
