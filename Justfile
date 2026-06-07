uitest:
    cargo nextest run --profile frontend-uitest

uitest-bless:
    FIR_FRONTEND_UI_TEST_BLESS=1 just uitest
