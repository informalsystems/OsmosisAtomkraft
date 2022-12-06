# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 3>>, <<"ujuno", 2>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 2>>, <<"ujuno", 3>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 3>>, <<"ujuno", 2>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 100000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 2>>, <<"ujuno", 3>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 2>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 100000000000000000001>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 3>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 7>>, <<"ujuno", 5>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 200000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 2>>, <<"ujuno", 3>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 0>>, <<"ujuno", 1>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 100000000000000000001>>, <<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 7>>, <<"ujuno", 5>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 200000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 2>>, <<"ujuno", 3>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 4>>, <<"ujuno", 4>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 0>>, <<"ujuno", 1>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({<<3, 100000000000000000000>>})>>, <<"C", SetAsFun({<<1, 100000000000000000001>>, <<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 3 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 7>>, <<"ujuno", 5>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 200000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 3, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

