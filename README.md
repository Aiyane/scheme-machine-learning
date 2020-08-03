从头实现机器学习，使用 delimited continuation 实现 automatic differentiation。并对一个梯度下降例子进行了测试，运行 linear-regression.ss 文件，输入 `(linear-regression)` 结果与 Python 中运行的结果一致。不过目前缺少矩阵运算的相关实现。

```
; 我的结果
(#(NumV 334302.06398245395)
 #(NumV 99411.44941267566)
 #(NumV 3267.0129025235187))

# python 中使用 numpy 运行的结果
[[334302.06399328]
[ 99411.44947359]
[  3267.01285407]]
```
