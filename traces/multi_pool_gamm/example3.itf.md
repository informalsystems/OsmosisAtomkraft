# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 1>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 50000000000000000000>>, <<"uosmo", 50000000000000000001>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 2 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 50000000000000000000>>, <<"uosmo", 50000000000000000001>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 50000000000000000000>>, <<"uosmo", 50000000000000000001>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 2>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 2>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000002, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 0>>, <<"ujuno", 49999999999999999999>>, <<"uosmo", 50000000000000000000>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 50000000000000000000>>, <<"uosmo", 50000000000000000001>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 100000000000000000000>>, <<2, 100000000000000000000>>})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 2>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 2>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000002, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

