default-uitest-pat := ""

uitest pat=default-uitest-pat:
    cargo nextest run --profile frontend-uitest -- "{{ pat }}"

uitest-bless pat=default-uitest-pat:
    CLAY_FRONTEND_UI_TEST_BLESS=1 just uitest "{{ pat }}"

uitest-list:
    cargo nextest list --profile frontend-uitest
