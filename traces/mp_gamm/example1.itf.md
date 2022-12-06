# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000000>>, <<"uosmo", 100000000000000000002>>}), sender \|-> "B", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 8>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000000>>, <<"uosmo", 100000000000000000002>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "A", share \|-> 1 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000007>>, <<"uosmo", 100000000000000000006>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 8>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 1>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 2>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000004>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000003>>}), sender \|-> "C", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000007>>, <<"uosmo", 100000000000000000006>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 8>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 7>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 1>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000004>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000003>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 2, sender \|-> "C", share \|-> 4 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000007>>, <<"uosmo", 100000000000000000006>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 8>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 2>>, <<"uosmo", 0>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 1>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000004>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"ujuno", 5>>, <<"uosmo", 5>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000004>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000006>>, <<"uosmo", 100000000000000000008>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000004, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

