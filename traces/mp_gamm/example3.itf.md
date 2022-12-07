# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 1>>}), sender \|-> "A", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 6>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 1>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "A", share \|-> 300000000000000000000 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 0>>, <<"uosmo", 4>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 400000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"ujuno", 6>>, <<"uosmo", 3>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 8>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 4>>}), sender \|-> "C", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 0>>, <<"uosmo", 4>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 6>>, <<"uosmo", 4>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 400000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 8>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 2, sender \|-> "B", share \|-> 25000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 0>>, <<"uosmo", 4>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 7>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 6>>, <<"uosmo", 4>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 400000000000000000000>>})>>, <<"B", SetAsFun({<<2, 25000000000000000001>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 2>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 8>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 3>>, <<"uosmo", 6>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 125000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

