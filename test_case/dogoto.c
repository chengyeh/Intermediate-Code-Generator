foo() {
    int a;
    a = 10;

    LOOP: do {

        if (a == 15) {
            a = a + 1;
            goto LOOP;
        }

        printf("value of a: %d\n", a);
        a = a + 1;

    } while (a < 20);

    LOOP:
    EXIT: a = 2;

    if(a == 2)
    {
      goto EXIT;
    }
    return 0;
}
