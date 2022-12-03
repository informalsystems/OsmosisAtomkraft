# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"C", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"C", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 1>>, <<"ujuno", 5>>, <<"uosmo", 7>>})>>, <<"C", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 1>>, <<"ujuno", 5>>, <<"uosmo", 7>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 2>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), sender \|-> "B", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 1>>, <<"ujuno", 4>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 2>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>, <<3, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 3 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "ExitPool", value \|-> [ id \|-> 1, sender \|-> "B", share \|-> 40000000000000000000 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 3>>, <<"ujuno", 5>>, <<"uosmo", 6>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 2>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 66666666666666666667>>, <<3, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "ExitPool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 1>>}), real_share \|-> 33333333333333333333 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 1>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 66666666666666666667, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 3, sender \|-> "B", share \|-> 200000000000000000001 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 3>>, <<"ujuno", 3>>, <<"uosmo", 4>>})>>, <<"C", SetAsFun({<<"uatom", 1>>, <<"ujuno", 2>>, <<"uosmo", 7>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 66666666666666666667>>, <<3, 300000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "JoinPool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 2>>}), real_share \|-> 200000000000000000000 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 4>>, <<"ujuno", 1>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 66666666666666666667, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 3>>, <<"uosmo", 3>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 300000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

