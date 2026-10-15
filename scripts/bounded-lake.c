/* Operational launcher; the pinned checking-tool implementations are unchanged. */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#ifndef REAL_LAKE
#error "Compile with the absolute path of the pinned Lake executable."
#endif

int main(int argc, char **argv) {
    (void)argc;
    if (setenv("LEAN_NUM_THREADS", "2", 1) != 0) {
        perror("setenv LEAN_NUM_THREADS");
        return 127;
    }
    execv(REAL_LAKE, argv);
    perror("execv pinned Lake");
    return 127;
}
