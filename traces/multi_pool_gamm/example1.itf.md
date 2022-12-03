# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 8>>, <<"ujuno", 3>>, <<"uosmo", 6>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 13>>, <<"ujuno", 18>>, <<"uosmo", 15>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 8>>, <<"ujuno", 3>>, <<"uosmo", 6>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "ExitPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 50000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 17>>, <<"ujuno", 20>>, <<"uosmo", 18>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 50000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "ExitPool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 2>>, <<"uosmo", 3>>}), real_share \|-> 50000000000000000000 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 1>>, <<"uosmo", 3>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 50000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 175000000000000000000 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 16>>, <<"uosmo", 6>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 250000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "JoinPool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 16>>, <<"ujuno", 4>>, <<"uosmo", 12>>}), real_share \|-> 200000000000000000000 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 20>>, <<"ujuno", 5>>, <<"uosmo", 15>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 250000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 16>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 0>>, <<"ujuno", 0>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 16>>, <<"uosmo", 6>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<2, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 250000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 20>>, <<"ujuno", 5>>, <<"uosmo", 15>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 250000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 16>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 4>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 0>>, <<"ujuno", 0>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 20>>, <<"ujuno", 20>>, <<"uosmo", 17>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 16>>, <<"uosmo", 6>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<2, 100000000000000000000>>})>>, <<"B", SetAsFun({<<3, 100000000000000000000>>})>>, <<"C", SetAsFun({<<1, 250000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 3 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 20>>, <<"ujuno", 5>>, <<"uosmo", 15>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 250000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 16>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 4>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

