void loop_example(int x, int y)
{
     __CPROVER_assume(x >= 0 && y >= 0 && y <= x);
	while (y != 0) { x--; y--; }
	assert(x >= 0);
}