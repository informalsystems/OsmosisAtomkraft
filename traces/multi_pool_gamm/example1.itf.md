# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"B", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"B", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 2>>, <<"uosmo", 5>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"B", SetAsFun({<<"uatom", 7>>, <<"ujuno", 9>>, <<"uosmo", 4>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ id \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 2>>, <<"uosmo", 5>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "A", share \|-> 160000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 5>>, <<"ujuno", 9>>, <<"uosmo", 0>>})>>, <<"B", SetAsFun({<<"uatom", 7>>, <<"ujuno", 9>>, <<"uosmo", 4>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 160000000000000000001>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", 4>>, <<"uosmo", 9>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"uosmo", 14>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 260000000000000000001, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "B", share \|-> 1 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 5>>, <<"ujuno", 9>>, <<"uosmo", 0>>})>>, <<"B", SetAsFun({<<"uatom", 6>>, <<"ujuno", 9>>, <<"uosmo", 3>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 160000000000000000001>>})>>, <<"B", SetAsFun({<<1, 100000000000000000001>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "UpdatePool", value \|-> [ deltas \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 7>>, <<"uosmo", 15>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 260000000000000000002, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

