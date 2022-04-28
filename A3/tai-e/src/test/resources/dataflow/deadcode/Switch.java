class Switch {
    void foo() {
        int x = 1;
        int y = x << 3;
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                use(4);
                break; // unreachable case
            default:
                use(666);
            case 10:
                if (x > y) {
                    use(233); // unreachable case
                } else {
                    use(789);
                    switch (x) {
                        case 1:
                            use(1010);
                        default:
                            use(1011);
                            break;
                        case 2:
                            use(3456); // unreachable case
                            break;
                    }
                }
        }
        int z = 42;
    }

    void use(int x) {

    }
}