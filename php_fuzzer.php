#!/usr/bin/env php
<?php
/**
 * To Install: `composer require nikic/php-parser:^2`
 * 
 * Random PHP code generator (PHP‑Parser 2.x / PHP 5.6).
 *   • Pure v2 API — no shim classes.
 *   • `--no-builtin` flag disables random built‑in calls.
 *   • Loop and branch bodies now always contain **assignment statements** (not just bare expressions).
 */

require __DIR__ . '/vendor/autoload.php';

use PhpParser\BuilderFactory;
use PhpParser\PrettyPrinter\Standard as Printer;
use PhpParser\Node;
use PhpParser\Node\Stmt;
use PhpParser\Node\Expr;

function ri($a, $b)
{
    return function_exists('random_int') ? random_int($a, $b) : mt_rand($a, $b);
} // RNG
function opts()
{
    return getopt('n::', ['print', 'easy', 'seed::', 'out::', 'no-builtin', 'wrap-builtin']);
}
function expr_stmt(Node $n)
{
    return $n;
} // v2 accepts raw Node stmt

function builtins()
{
    $tbl = [];
    foreach (get_defined_functions()['internal'] as $fn) {
        if (strpos($fn, 'php_') === 0 || in_array($fn, ['exit', 'die'])) continue;
        $r = new ReflectionFunction($fn);
        $min = $r->getNumberOfRequiredParameters();
        $max = $r->getNumberOfParameters();
        if ($max === 0) continue;
        $tbl[$fn] = [$min, $max ?: $min];
    }
    return $tbl;
}
$BUILT = builtins();

function make_expr_gen(array &$vars, array &$built, $use, $wrap)
{
    $g = null;
    $g = function ($d = 0) use (&$g, &$vars, &$built, $use, $wrap) {
        if ($use && $d > 0 && ri(1, 100) <= 25) {
            $fn = array_rand($built);
            list($min, $max) = $built[$fn];
            $argc = ri($min, min($max, 4));
            $args = [];
            $arr = [];
            for ($i = 0; $i < $argc; $i++) {
                $e = $d > 2 ? new Node\Scalar\LNumber(ri(-20, 20)) : ($i === 0 ? new Expr\Variable($vars[array_rand($vars)]) : new Node\Scalar\LNumber(ri(-50, 50)));
                $args[] = $e;
                $arr[] = new Expr\ArrayItem($e);
            }
            return $wrap ?
                new Expr\FuncCall(new Node\Name('wrapper'), [
                    new Node\Scalar\String_($fn),
                    new Expr\Array_($arr)
                ]) :
                new Expr\FuncCall(new Node\Name($fn), $args);
        }
        if ($d > 2 || ri(0, 1) == 0) {
            return ri(0, 1) ? new Expr\Variable($vars[array_rand($vars)])
                : new Node\Scalar\LNumber(ri(-5000, 5000));
        }
        $ops = ['Plus', 'Minus', 'Mul', 'Div', 'Mod', 'BitwiseXor', 'BitwiseOr', 'BitwiseAnd'];
        $cls = 'PhpParser\\Node\\Expr\\BinaryOp\\' . $ops[array_rand($ops)];
        return new $cls($g($d + 1), $g($d + 1));
    };
    return $g;
}

function gen_program($easy, array &$built, $use, $wrap)
{
    $f = new BuilderFactory();
    $s = [];
    $vars = [];
    for ($i = 0, $n = $easy ? ri(2, 4) : ri(3, 8); $i < $n; $i++) {
        $v = chr(ri(97, 122)) . ri(0, 99);
        $vars[] = $v;
        $s[] = expr_stmt(new Expr\Assign(new Expr\Variable($v), new Node\Scalar\LNumber(ri(-5000, 5000))));
    }
    $g = make_expr_gen($vars, $built, $use, $wrap);
    $assign = function () use (&$vars, &$g) {
        $t = $vars[array_rand($vars)];
        return expr_stmt(new Expr\Assign(new Expr\Variable($t), $g()));
    };

    for ($i = 0, $c = $easy ? ri(4, 6) : ri(6, 15); $i < $c; $i++) {
        ($i & 1) ? $s[] = $assign() : $s[] = $g();
        if (ri(0, 1) == 0) $s[] = new Stmt\If_($g(), ['stmts' => [$assign()]]);
        if (ri(0, 1) == 0) {
            if (ri(0, 1) == 0) {
                $lv = 'i' . ri(0, 99);
                $init = [new Expr\Assign(new Expr\Variable($lv), new Node\Scalar\LNumber(0))];
                $cond = [new Expr\BinaryOp\Smaller(new Expr\Variable($lv), new Node\Scalar\LNumber(ri(2, 10)))];
                $step = [new Expr\PostInc(new Expr\Variable($lv))];
                $s[] = new Stmt\For_(['init' => $init, 'cond' => $cond, 'loop' => $step, 'stmts' => [$assign()]]);
            } else $s[] = new Stmt\While_($g(), [$assign()]);
        }
    }
    $s[] = new Stmt\Return_(new Expr\Variable($vars[array_rand($vars)]));
    $main = $f->function('main')->addStmts($s)->getNode();
    return (new Printer())->prettyPrintFile([$main, new Expr\FuncCall(new Node\Name('main'))]);
}

function write_p($c, $d, $i)
{
    if (!is_dir($d) && !mkdir($d, 0777, true)) die('mkdir');
    $p = rtrim($d, '/\\') . "/prog_$i.php";
    file_put_contents($p, $c);
    return $p;
}

function main(array &$b)
{
    $o = opts();
    $e = isset($o['easy']);
    $u = !isset($o['no-builtin']);
    $w = true;
    if (isset($o['seed']) && $o['seed'] !== false) {
        mt_srand((int)$o['seed']);
    }
    if (!isset($o['n']) || isset($o['print'])) {
        echo gen_program($e, $b, $u, $w), "\n";
        return;
    }
    $n = (int)$o['n'];
    $out = (isset($o['out']) && $o['out'] !== false) ? $o['out'] : __DIR__ . '/generated';
    for ($i = 1; $i <= $n; $i++) echo write_p(gen_program($e, $b, $u, $w), $out, $i) . "\n";
}

main($BUILT);
