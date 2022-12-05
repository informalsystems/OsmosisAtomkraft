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
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 1>>, <<"uosmo", 3>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 2>>, <<"ujuno", 7>>, <<"uosmo", 5>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 1>>, <<"uosmo", 3>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 1 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 6>>, <<"uosmo", 4>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 100000000000000000001>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 7>>, <<"ujuno", 2>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "ExitPool", value \|-> [ id \|-> 1, sender \|-> "C", share \|-> 50000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 4>>, <<"ujuno", 7>>, <<"uosmo", 6>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({<<1, 50000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", -3>>, <<"ujuno", -1>>, <<"uosmo", -2>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 1>>, <<"uosmo", 2>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 50000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

